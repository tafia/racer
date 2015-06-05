use std::fs::File;
use std::io::{BufReader, Read};
use std::{str, vec, fmt};
use std::path;

pub mod scopes;
pub mod ast;
pub mod typeinf;
pub mod nameres;
pub mod codeiter;
pub mod codecleaner;
pub mod testutils;
pub mod util;
pub mod matchers;
pub mod snippets;
pub mod cargo;

#[cfg(test)] pub mod test;
#[cfg(test)] pub mod bench;

#[derive(Debug,Copy,Clone,PartialEq)]
pub enum MatchType {
    Struct,
    Module,
    MatchArm,
    Function,
    Crate,
    Let,
    IfLet,
    StructField,
    Impl,
    Enum,
    EnumVariant,
    Type,
    FnArg,
    Trait,
    Const,
    Static
}

#[derive(Debug,Copy,Clone)]
pub enum SearchType {
    ExactMatch,
    StartsWith
}

#[derive(Debug,Copy,Clone)]
pub enum Namespace {
    TypeNamespace,
    ValueNamespace,
    BothNamespaces
}

#[derive(Debug,Copy,Clone)]
pub enum CompletionType {
    CompleteField,
    CompletePath
}

#[derive(Clone)]
pub struct Match {
    pub matchstr: String,
    pub filepath: path::PathBuf,
    pub point: usize,
    pub local: bool,
    pub mtype: MatchType,
    pub contextstr: String,
    pub generic_args: Vec<String>,
    pub generic_types: Vec<PathSearch>  // generic types are evaluated lazily
}

impl Match {

    fn new<SM, SC, P>(matchstr: SM, path: P, point: usize, local: bool, 
                 mtype: MatchType, context: SC) -> Match 
        where SM: Into<String>,
              SC: Into<String>,
              P: Into<path::PathBuf> 
    {
        Match {
            matchstr: matchstr.into(),
            filepath: path.into(),
            point: point,
            local: local,
            mtype: mtype,
            contextstr: context.into(),
            generic_args: Vec::new(),
            generic_types: Vec::new()
        }
    }

    fn with_generic_types(&self, generic_types: Vec<PathSearch>) -> Match {
        Match {
            matchstr: self.matchstr.clone(),
            filepath: self.filepath.clone(),
            point: self.point,
            local: self.local,
            mtype: self.mtype,
            contextstr: self.contextstr.clone(),
            generic_args: self.generic_args.clone(),
            generic_types: generic_types
        }
    }
}

impl fmt::Debug for Match {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Match [{:?}, {:?}, {:?}, {:?}, {:?}, {:?}, {:?} |{}|]",
               self.matchstr,
               self.filepath.to_str(),
               self.point,
               self.local,
               self.mtype,
               self.generic_args,
               self.generic_types,
               self.contextstr)
    }
}

#[derive(Clone)]
pub struct Scope {
    pub filepath: path::PathBuf,
    pub point: usize
}

impl Scope {
    pub fn from_match(m: &Match) -> Scope {
        Scope{ filepath: m.filepath.clone(), point: m.point }
    }
}

impl fmt::Debug for Scope {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Scope [{:?}, {:?}]",
               self.filepath.to_str(),
               self.point)
    }
}

// Represents a type. Equivilent to rustc's ast::Ty but can be passed across threads
#[derive(Debug,Clone)]
pub enum Ty {
    TyMatch(Match),
    TyPathSearch(Path, Scope),   // A path + the scope to be able to resolve it
    TyTuple(Vec<Ty>),
    TyUnsupported
}

// The racer implementation of an ast::Path. Difference is that it is Send-able
#[derive(Clone)]
pub struct Path {
    global: bool,
    segments: Vec<PathSegment>
}

impl Path {
    pub fn generic_types(&self) -> ::std::slice::Iter<Path> {
        self.segments[self.segments.len()-1].types.iter()
    }

    pub fn from_vec<S: Into<String>>(global: bool, v: Vec<S>) -> Path {
        Path{ 
            global: global, 
            segments: v.into_iter().map(|x| PathSegment::new(x)).collect() 
        }
    }
}

impl fmt::Debug for Path {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "P["));
        let mut first = true;
        for seg in self.segments.iter() {
            if first {
                try!(write!(f, "{}", seg.name));
                first = false;
            } else {
                try!(write!(f, "::{}", seg.name));
            }

            if !seg.types.is_empty() {
                try!(write!(f, "<"));
                let mut tfirst = true;
                for typath in seg.types.iter() {
                    if tfirst {
                        try!(write!(f, "{:?}", typath));
                        tfirst = false;
                    } else {
                        try!(write!(f, ",{:?}", typath))
                    }
                }
                try!(write!(f, ">"));
            }
        }
        write!(f, "]")
    }
}

#[derive(Debug,Clone)]
pub struct PathSegment {
    pub name: String,
    pub types: Vec<Path>
}

impl PathSegment {
    fn new<S: Into<String>>(name: S) -> PathSegment {
        PathSegment { name: name.into(), types: Vec::new() }
    }
}

#[derive(Clone)]
pub struct PathSearch {
    path: Path,
    filepath: path::PathBuf,
    point: usize
}

impl fmt::Debug for PathSearch {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Search [{:?}, {:?}, {:?}]",
               self.path,
               self.filepath.to_str(),
               self.point)
    }
}

pub fn load_file(filepath: &path::Path) -> String {
    File::open(filepath).ok().map_or("".to_string(), |f| {
        let mut rawbytes = Vec::new();
        BufReader::new(f).read_to_end(&mut rawbytes).unwrap();

        // skip BOF bytes, if present
        if rawbytes[0..3] == [0xEF, 0xBB, 0xBF] {
            String::from_utf8(rawbytes.into_iter().skip(3).collect()).unwrap()
        } else {
            String::from_utf8(rawbytes).unwrap()
        }
    })
}

pub fn load_file_and_mask_comments(filepath: &path::Path) -> String {
    let mut filetxt = Vec::new();
    BufReader::new(File::open(filepath).unwrap()).read_to_end(&mut filetxt).unwrap();
    let src = str::from_utf8(&filetxt).unwrap();

    scopes::mask_comments(src)
}

pub fn complete_from_file(src: &str, filepath: &path::Path, pos: usize) -> vec::IntoIter<Match> {
    let start = scopes::get_start_of_search_expr(src, pos);
    search_expressions(&src[start..pos], filepath, pos, SearchType::StartsWith)
}

pub fn find_definition(src: &str, filepath: &path::Path, pos: usize) -> Option<Match> {
    find_definition_(src, filepath, pos)
}

pub fn find_definition_(src: &str, filepath: &path::Path, pos: usize) -> Option<Match> {
    let (start, end) = scopes::expand_search_expr(src, pos);
    search_expressions(&src[start..end], filepath, pos, SearchType::ExactMatch).next()
}


fn search_expressions(expr: &str, filepath: &path::Path, pos: usize, search_type: SearchType)
        -> vec::IntoIter<Match> {

    let (contextstr, searchstr, completetype) = scopes::split_into_context_and_completion(expr);
    debug!("search_expr_from_file for |{:?}| |{:?}| {:?}", contextstr, searchstr, completetype);

    match completetype {
        CompletionType::CompletePath => {
            let global = expr.starts_with("::"); // e.g. ::std::old_io::blah
            let v = (if global { &expr[2..] } else { expr }).split("::").collect();
            nameres::resolve_path(&Path::from_vec(global, v), filepath, pos,
                                  search_type, Namespace::BothNamespaces)
        },
        CompletionType::CompleteField => {
            let context = ast::get_type_of(contextstr.to_string(), filepath, pos);
            debug!("context is {:?}", context);

            context.map_or(Vec::new().into_iter(), |ty| {
                // for now, just handle matches
                if let Ty::TyMatch(m) = ty {
                    nameres::search_for_field_or_method(m, searchstr, search_type)
                } else {
                    Vec::new().into_iter()
                }
            })
        }
    }     
}