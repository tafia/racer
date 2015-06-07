// Name resolution

use racer::{self, ast, codeiter, matchers, scopes, typeinf, util, cargo, Match};
use racer::SearchType::{self, ExactMatch, StartsWith};
use racer::MatchType::{Module, Function, Struct, Enum, FnArg, Trait, StructField, Impl, MatchArm, Undef};
use racer::Namespace::{self, TypeNamespace, ValueNamespace, BothNamespaces};
use racer::util::{symbol_matches, txt_matches, find_ident_end, path_exists};
use std::fs::File;
use std::ops::Deref;
use std::path::{Path, PathBuf};
use std::{self, vec};

#[cfg(unix)]
pub const PATH_SEP: &'static str = ":";
#[cfg(windows)]
pub const PATH_SEP: &'static str = ";";

fn search_struct_fields<'a>(searchstr: &'a str, m: &'a Match, search_type: SearchType)
        -> Box<Iterator<Item=Match> + 'a> {

    let opoint = scopes::find_stmt_start(&*m.src, m.point).unwrap();
    let structsrc = scopes::end_of_next_scope(&m.src[opoint..]);

    Box::new(ast::parse_struct_fields(structsrc.to_string(), 
             racer::Scope::from_match(m))
    .into_iter().filter_map(move |(ref field, fpos, _)| 
        if symbol_matches(search_type, searchstr, &field) {
            let mut m = m.clone();
            m.matchstr = field.to_string();
            m.point = fpos + opoint;
            m.mtype = StructField;
            m.contextstr = m.matchstr.clone();
            Some(m)
        } else { 
            None 
        }))
}

pub fn search_for_impl_methods<'a>(m: &'a Match, fieldsearchstr: &'a str, 
                                   search_type: SearchType) -> Box<Iterator<Item=Match> + 'a> {

    debug!("searching for impl methods |{}| |{}| {:?}", 
           m.matchstr, fieldsearchstr, m.filepath.to_str());

    // return a box iterator
    // must collect all methods (probably cheap enough) to workaround lifetime issues
    Box::new(ImplIter::new(m, true)
        .flat_map(move |m| MethodIter::new(&m, fieldsearchstr, search_type)
            .collect::<Vec<_>>().into_iter()))
}

enum IterState<'a> {
    Uninitialized,
    Iterating(usize, codeiter::StmtIndicesIter<'a>),

}

struct MethodIter<'a> {
    m: &'a Match,
    state: IterState<'a>,
    searchfn: String,
    search_type: SearchType
}

impl<'a> MethodIter<'a> {
    fn new(m: &'a Match, searchstr: &str, search_type: SearchType) -> MethodIter<'a> {
        MethodIter { 
            m: m, 
            state: IterState::Uninitialized, 
            searchfn: format!("fn {}", searchstr), 
            search_type: search_type 
        }
    }
}

impl<'a> Iterator for MethodIter<'a> {
    type Item=Match;

    fn next(&mut self) -> Option<Match> {
        loop {
            match self.state {
                IterState::Uninitialized => {
                    if let Some(n) = self.m.src[self.m.point..].find('{') {
                        let point = self.m.point + n + 1;
                        debug!("searching scope for methods {} |{}| {:?}", 
                            point, self.searchfn, self.m.filepath);
                        let src = &self.m.src[point..];
                        self.state = IterState::Iterating(point, codeiter::iter_stmts(src));
                    } else {
                        return None;
                    }
                },
                IterState::Iterating(point, ref mut iter) => {
                    loop {
                        if let Some((blobstart,blobend)) = iter.next() {
                            let blob = &self.m.src[point+blobstart..point+blobend];
                            if txt_matches(self.search_type, &self.searchfn, blob)
                                && typeinf::first_param_is_self(blob) {

                                debug!("found a method starting |{}| |{}|", self.searchfn, blob);

                                // TODO: parse this properly
                                let start = blob.find(&self.searchfn).unwrap() + 3;
                                let end = find_ident_end(blob, start);
                                let l = &blob[start..end];

                                // TODO: make a better context string for functions
                                // only matches if is a method implementation
                                if let Some(n) = blob.find('{') {
                                    let mut m = self.m.clone();
                                    m.matchstr = l.to_string();
                                    m.point = point + blobstart + start;
                                    m.local = true;
                                    m.mtype = Function;
                                    m.contextstr = blob[..n -1].to_owned();
                                    return Some(m);
                                }
                            }
                        } else {
                            return None;
                        }
                    }
                }
            }
        }
    }
}

struct ImplIter<'a> {
    m: &'a Match,
    state: IterState<'a>,
    include_traits: bool,
    trait_path: Option<racer::Path>,
}

impl<'a> ImplIter<'a> {
    fn new(m: &'a Match, include_traits:bool) -> ImplIter<'a> {
        ImplIter { 
            m:m,
            state: IterState::Uninitialized, 
            include_traits: include_traits, 
            trait_path: None,
        }
    }
}

impl<'a> Iterator for ImplIter<'a> {
    type Item=Match;

    fn next(&mut self) -> Option<Match> {
        loop {
            match self.state {
                IterState::Uninitialized => {
                    self.state = IterState::Iterating(0, 
                        codeiter::iter_stmts(&self.m.src[self.m.point..]))
                }
                // must iterate on code
                IterState::Iterating(ref mut pos, ref mut iter) if *pos == 0 => {
                    if let Some((start, end)) = iter.next() {
                        let blob = &self.m.src[start+self.m.point..end+self.m.point];
                        if blob.starts_with("impl") {
                            if let Some(n) = blob.find('{') {
                                let mut decl = (&blob[..n+1]).to_string();
                                decl.push('}');
                                if txt_matches(ExactMatch, &self.m.matchstr, &decl) {

                                    debug!("impl decl {}", decl);
                                    let implres = ast::parse_impl(decl);

                                    if self.include_traits { 
                                        self.trait_path = implres.trait_path;
                                        *pos = self.m.point + start;
                                    }

                                    if let Some(name_path) = implres.name_path {
                                        if let Some(name) = name_path.segments.last() {
                                            let mut m = self.m.clone();
                                            m.matchstr = name.name.clone();
                                            m.point += start + 5;
                                            m.mtype = Impl;
                                            m.contextstr = "".to_string();
                                            return Some(m);
                                        }
                                    }
                                }
                            }
                        }
                    } else { 
                        return None;
                    }
                }
                IterState::Iterating(ref mut pos, _) => {
                    if let Some(ref trait_path) = self.trait_path {
                        if let Some(m) = resolve_path(&trait_path, &*self.m.filepath, 
                                            *pos, ExactMatch, 
                                            TypeNamespace).next() {
                            debug!("found trait |{:?}| {:?}", trait_path, m);
                            *pos = 0;
                            return Some(m);
                        }
                    }
                    *pos = 0;
                }
            }
        }
    }
}

// scope headers include fn decls, if let, while let etc..
fn search_scope_headers(m: &Match, scopestart: usize, search_type: SearchType)     
    -> vec::IntoIter<Match> {

    debug!("search_scope_headers for |{}| pt: {}", m.matchstr, scopestart);

    scopes::find_stmt_start(&&*m.src, scopestart).map_or(Vec::new().into_iter(), |stmtstart| {

        let preblock = &m.src[stmtstart..scopestart];
        debug!("PHIL search_scope_headers preblock is |{}|", preblock);

        if preblock.starts_with("fn") || preblock.starts_with("pub fn") {
            return search_fn_args(stmtstart, scopestart, &&*m.src, &m.matchstr, 
                                  &m.filepath, search_type, m.local);

        // 'if let' can be an expression, so might not be at the start of the stmt
        } else if let Some(n) = preblock.find("if let") {
            let ifletstart = stmtstart + n;
            let s = (&m.src[ifletstart..scopestart+1]).to_string() + "}";
            if txt_matches(search_type, &m.matchstr, &*s) {
                let mut out = matchers::match_if_let(&*s, 0, s.len(), &m.matchstr,
                                                     &m.filepath, search_type, m.local);
                for m in out.iter_mut() {
                    m.point += ifletstart;
                }
                out
            } else { Vec::new() }
        } else if let Some(n) = util::find_last_str("match ", preblock) {
            // TODO: this code is crufty. refactor me!
            let matchstart = stmtstart + n;
            let matchstmt = typeinf::get_first_stmt(&m.src[matchstart..]);
            // The definition could be in the match LHS arms. Try to find this
            debug!("PHIL found a match statement, examining match arms (len {}) |{}|",
                   matchstmt.len(), matchstmt);

            let masked_matchstmt = mask_matchstmt(matchstmt, scopestart + 1 - matchstart);
            debug!("PHIL masked match stmt is len {} |{}|", masked_matchstmt.len(), masked_matchstmt);

            // Locate the match arm LHS by finding the => just before point and then backtracking
            let mut rhs = &*masked_matchstmt;
            let mut arm = 0;
            while let Some(n) = rhs.find("=>") {
                debug!("PHIL match arm n is {}, {}, {}, {}", arm, n, matchstart, m.point);
                if arm + n + matchstart > m.point {
                    break;
                } else {
                    arm += n + 2;
                    rhs = &rhs[n+2..];
                }
            }
            debug!("PHIL matched arm rhs is |{}|", &masked_matchstmt[arm-2..]);

            let lhs_start = scopes::get_start_of_pattern(&&*m.src, matchstart + arm - 2);
            let lhs = &m.src[lhs_start..matchstart + arm - 2];

            // Now create a pretend match expression with just the one match arm in it
            let mut fauxmatchstmt = (&m.src[matchstart..scopestart]).to_string();
            fauxmatchstmt = fauxmatchstmt + "{";
            let faux_prefix_size = fauxmatchstmt.len();
            fauxmatchstmt = fauxmatchstmt + lhs + " => () };";

            debug!("PHIL arm lhs is |{}|", lhs);
            debug!("PHIL arm fauxmatchstmt is |{}|, {}", fauxmatchstmt, faux_prefix_size);
            let mut matches = ast::parse_pat_idents(fauxmatchstmt)
            .into_iter().filter_map(|(start,end)| {
                let (start, end) = (lhs_start + start - faux_prefix_size,
                                   lhs_start + end - faux_prefix_size);
                let s = &m.src[start..end];

                if symbol_matches(search_type, &m.matchstr, s) {
                    let mut m = m.clone();
                    m.matchstr = s.to_string();
                    m.point = start;
                    m.mtype = MatchArm;
                    m.contextstr = lhs.trim().to_string();
                    Some(m)
                } else {
                    None
                }
            });
            match search_type {
                ExactMatch => matches.next().map_or(Vec::new(), |m| vec![m]),
                StartsWith => matches.collect::<Vec<_>>()
            }
        } else {
           Vec::new()
        }.into_iter()
    })

}

fn mask_matchstmt(matchstmt_src: &str, innerscope_start: usize) -> String {
    let s = scopes::mask_sub_scopes(&matchstmt_src[innerscope_start..]);
    (&matchstmt_src[..innerscope_start]).to_string() + &*s
}

#[test]
fn does_it() {
    let src : &str = "
    match foo {
        Some(a) => { something }
    }";
    let res = mask_matchstmt(src, src.find('{').unwrap()+1);
    debug!("PHIL res is |{}|",res);
}

fn search_fn_args(fnstart: usize, open_brace_pos: usize, msrc:&str, searchstr:&str,
                   filepath:&Path,
                   search_type: SearchType, local: bool) -> vec::IntoIter<Match> {
    let mut fndecl = String::new();
    // wrap in 'impl blah {}' so that methods get parsed correctly too
    fndecl.push_str("impl blah {");
    let impl_header_len = fndecl.len();
    fndecl.push_str(&msrc[fnstart..(open_brace_pos + 1)]);
    fndecl.push_str("}}");
    debug!("search_fn_args: found start of fn!! {} |{}| {}", fnstart, fndecl, searchstr);
    if txt_matches(search_type, searchstr, &fndecl) {
        ast::parse_fn_args(fndecl.clone()).into_iter().filter_map(|(start, end)| {
            let s = &fndecl[start..end];
            debug!("search_fn_args: arg str is |{}|", s);
            if symbol_matches(search_type, searchstr, s) {
                Some(Match::new(s, filepath, start + fnstart - impl_header_len, local, FnArg, s))
            } else {
                None
            }
        }).collect::<Vec<_>>().into_iter()
    } else {
        Vec::new().into_iter()
    }
}

pub fn do_file_search(searchstr: &str, currentdir: &Path) -> vec::IntoIter<Match> {
    debug!("do_file_search {}", searchstr);
    let mut out = Vec::new();

    let srcpaths = std::env::var("RUST_SRC_PATH").unwrap_or("".to_string());
    debug!("do_file_search srcpaths {}", srcpaths);
    let mut v = srcpaths.split(PATH_SEP).collect::<Vec<_>>();
    v.push(currentdir.to_str().unwrap());
    debug!("do_file_search v is {:?}", v);
    for srcpath in v.into_iter() {
        if let Ok(iter) = std::fs::read_dir(&Path::new(srcpath)) {

            let files = iter.filter_map(|dir_entry_result|
                if let Ok(dir_entry) = dir_entry_result {
                    Some(dir_entry.path())
                } else { None });

            for fpath_buf in files {
                let fname = fpath_buf.deref().file_name().unwrap().to_str().unwrap();
                if fname.starts_with(&format!("lib{}", searchstr)) {
                    let filepath = fpath_buf.deref().join("lib.rs");
                    if File::open(&filepath).is_ok() {
                        out.push(Match::new(&fname[3..], filepath, 0, false, 
                                            Module, &fname[3..]));
                    }
                } else if fname.starts_with(searchstr) {

                    // try <name>/<name>.rs, like in the servo codebase
                    // try <name>/mod.rs
                    // try <name>/lib.rs
                    out.extend([&*format!("{}.rs", fname), "mod.rs", "lib.rs"]
                               .into_iter().filter_map(|f| {
                        let filepath = fpath_buf.deref().join(f);
                        if File::open(&filepath).is_ok() {
                            let ctxt = filepath.to_str().unwrap();
                            Some(Match::new(fname, &filepath, 0, false, Module, ctxt))
                        } else {
                            None
                        }
                    }));

                    // try just <name>.rs
                    if fname.ends_with(".rs") {
                        out.push(Match::new(&fname[..(fname.len()-3)], 
                                            &fpath_buf, 0, false, Module, 
                                            fpath_buf.deref().to_str().unwrap()));
                    }
                }
            }
        }
    }
    out.into_iter()
}

pub fn search_crate_root(pathseg: &racer::PathSegment, modfpath: &Path,
                         searchtype: SearchType, namespace: Namespace) -> vec::IntoIter<Match> {
    debug!("search_crate_root |{:?}| {:?}", pathseg, modfpath.to_str());

    let crateroots = find_possible_crate_root_modules(&modfpath.parent().unwrap());

    let mut matches = crateroots.into_iter()
        .find(|crateroot| crateroot.deref() != modfpath)
        .map_or(Vec::new().into_iter(), |ref crateroot| {
            debug!("going to search for {:?} in crateroot {:?}", pathseg, crateroot.to_str());
            resolve_name(pathseg, crateroot, 0, searchtype, namespace)
        });

    match searchtype {
        ExactMatch => matches.next().map_or(Vec::new(), |m| vec![m]).into_iter(),
        StartsWith => matches
    }
}

pub fn find_possible_crate_root_modules(currentdir: &Path) -> Vec<PathBuf> {
    
    let filenames = ["lib.rs", "main.rs"];
    let mut files = filenames.into_iter().filter_map(|f| {        
        let filepath = currentdir.join(f);
        if File::open(&filepath).is_ok() {
            Some(filepath.to_owned())
        } else {
            None
        }
    });

    match files.next() {
        Some(f) => vec![f], // for now stop at the first match
        None => {
            if let Some(parentdir) = currentdir.parent() {
                if parentdir != currentdir {
                    // for now stop at the first match so we can return directly
                    return find_possible_crate_root_modules(&parentdir);
                }
            }
            Vec::new()
        }
    }
}

fn search_next_scope(m: &mut Match, search_type: SearchType, namespace: Namespace) 
        -> vec::IntoIter<Match> {

    let mut point = m.point;
    if point != 0 {
        // is a scope inside the file. Point should point to the definition
        // (e.g. mod blah {...}), so the actual scope is past the first open brace.
        let src = &m.src[point..];
        //debug!("search_next_scope src1 |{}|",src);
        // find the opening brace and skip to it.
        src.find('{').map(|n| {
            point += n + 1;
        });
    }
    m.point = point;
    search_scope(&m, m.point, search_type, namespace)
}

pub fn get_crate_file(name: &str, from_path: &Path) -> Option<PathBuf> {
    debug!("get_create_file {}", name);
    if let Some(p) = cargo::get_crate_file(name, from_path) {
        return Some(p);
    }

    let filenames = [&*format!("lib{}", name), name];
    let srcpaths = std::env::var("RUST_SRC_PATH").unwrap();

    (&srcpaths).split(PATH_SEP).into_iter().map(|srcpath| {
        filenames.into_iter().filter_map(|path| {
            let filepath = Path::new(srcpath).join(path).join("lib.rs");
            if File::open(&filepath).is_ok() {
                Some(filepath.to_path_buf())
            } else {
                None
            }
        }).next()
    }).next().unwrap_or(None)
}

pub fn get_module_file(name: &str, parentdir: &Path) -> Option<PathBuf> {
    {
        // try just <name>.rs
        let filepath = parentdir.join(format!("{}.rs", name));
        if File::open(&filepath).is_ok() {
            return Some(filepath.to_path_buf());
        }
    }
    {
        // try <name>/mod.rs
        let filepath = parentdir.join(name).join("mod.rs");
        if File::open(&filepath).is_ok() {
            return Some(filepath.to_path_buf());
        }
    }
    None
}

fn search_scope(m: &Match, start: usize,  search_type: SearchType, namespace: Namespace) 
        -> vec::IntoIter<Match> {

    let mut out = Vec::new();

    debug!("searching scope {:?} start: {} point: {} '{}' {:?} {:?} local: {}",
           namespace, start, m.point, m.matchstr, m.filepath.to_str(), search_type, m.local);

    let scopesrc = &m.src[start..];
    let mut skip_next_block = false;
    let mut delayed_use_globs = Vec::new();
    let mut codeit = codeiter::iter_stmts(scopesrc);
    let mut v = Vec::new();

    // collect up to point so we can search backwards for let bindings
    //  (these take precidence over local fn declarations etc..
    for (blobstart, blobend) in &mut codeit {
        //  (e.g. #[cfg(test)])
        if skip_next_block {
            skip_next_block = false;
            continue;
        }

        let blob = &scopesrc[blobstart..blobend];

        // for now skip stuff that's meant for testing. Often the test
        // module hierarchy is incompatible with the non-test
        // hierarchy and we get into recursive loops
        if blob.starts_with("#[cfg(test)") {
            skip_next_block = true;
            continue;
        }

        v.push((blobstart,blobend));

        if blobstart > m.point {
            break;
        }
    }

    // search backwards from point for let bindings
    for &(blobstart, blobend) in v.iter().rev() {
        if (start+blobend) >= m.point {
            continue;
        }

        for m in matchers::match_let(&&*m.src, start+blobstart,
                                     start+blobend,
                                     &m.matchstr,
                                     &*m.filepath, search_type, m.local).into_iter() {
            out.push(m);
            if let ExactMatch = search_type {
                return out.into_iter();
            }
        }
    }
    // now search from top of scope for items etc..
    let mut codeit = v.into_iter().chain(codeit);
    for (blobstart, blobend) in &mut codeit {
        // sometimes we need to skip blocks of code if the preceeding attribute disables it
        //  (e.g. #[cfg(test)])
        if skip_next_block {
            skip_next_block = false;
            continue;
        }

        let blob = &scopesrc[blobstart..blobend];

        // for now skip stuff that's meant for testing. Often the test
        // module hierarchy is incompatible with the non-test
        // hierarchy and we get into recursive loops
        if blob.starts_with("#[cfg(test)") {
            skip_next_block = true;
            continue;
        }

        let is_a_use_glob = (blob.starts_with("use") || blob.starts_with("pub use"))
              && blob.find("::*").is_some();

        if is_a_use_glob {
            // globs are *really* expensive to process. delay them until later
            delayed_use_globs.push((blobstart, blobend));
            continue;
        }

        // Optimisation: if the search string is not in the blob and it is not
        // a 'use glob', this cannot match so fail fast!
        if blob.find(&m.matchstr).is_none() {
            continue;
        }

        // There's a good chance of a match. Run the matchers
        out.extend(run_matchers_on_blob(&&*m.src, start+blobstart, start+blobend,
                                        &m.matchstr,
                                        &*m.filepath, search_type, m.local, namespace));
        if let ExactMatch = search_type {
            if !out.is_empty() {
                return out.into_iter();
            }
        }
    }

    // finally process any use-globs that we skipped before
    for &(blobstart, blobend) in delayed_use_globs.iter() {
        // There's a good chance of a match. Run the matchers
        for m in run_matchers_on_blob(&&*m.src, start+blobstart, start+blobend,
                                      &m.matchstr, &*m.filepath, search_type,
                                      m.local, namespace).into_iter() {
            out.push(m);
            if let ExactMatch = search_type {
                return out.into_iter();
            }
        }
    }

    debug!("search_scope found matches {:?} {:?}", search_type, out);
    out.into_iter()
}

fn run_matchers_on_blob<'a>(src: &'a str, start: usize, end: usize, searchstr: &'a str,
                            filepath: &'a Path, search_type: SearchType, local: bool,
                            namespace: Namespace) -> Box<Iterator<Item=Match> + 'a> {

    let mut iter = match namespace {
        TypeNamespace => {
            Box::new(matchers::match_types(src, start, end, searchstr, 
                                           filepath, search_type, local))
            as Box<Iterator<Item=Match> + 'a>
        },
        ValueNamespace => {
            Box::new(matchers::match_values(src, start, end, searchstr, 
                                            filepath, search_type, local))
            as Box<Iterator<Item=Match> + 'a>
        },
        BothNamespaces => {
            Box::new(matchers::match_types(src, start, end, searchstr, 
                                           filepath, search_type, local)
                     .chain(matchers::match_values(src, start, end, searchstr,
                                                   filepath, search_type, local)))
            as Box<Iterator<Item=Match> + 'a>
        }
    };

    match search_type {
        ExactMatch => Box::new(iter.next().map_or(Vec::new(), |m| vec![m]).into_iter())
            as Box<Iterator<Item=Match> + 'a>,
        StartsWith => iter
    }
}

fn search_local_scopes(m: &mut Match, search_type: SearchType, namespace: Namespace) 
        -> vec::IntoIter<Match> {

    debug!("search_local_scopes {:?} {:?} {} {:?} {:?}", m.matchstr, m.filepath.to_str(), 
        m.point, search_type, namespace);

    m.local = true;
    if m.point == 0 {
        // search the whole file
        search_scope(&m, 0, search_type, namespace)
    } else {
        let mut out = Vec::new();
        let mut start = m.point;
        // search each parent scope in turn
        while start > 0 {
            start = scopes::scope_start(&&*m.src, start);

            let mut scopes = search_scope(&m, start, search_type, namespace);
            match search_type {
                ExactMatch => {
                    if let Some(m) = scopes.next() {
                        return vec![m].into_iter();
                    }
                },
                StartsWith => out.extend(scopes)
            }

            if start == 0 {
                break;
            }

            start -= 1;

            // scope headers = fn decls, if let, match, etc..
            scopes = search_scope_headers(&m, start, search_type);
            match search_type {
                ExactMatch => {
                    if let Some(m) = scopes.next() {
                        return vec![m].into_iter();
                    }
                },
                StartsWith => out.extend(scopes)
            }
        }
        out.into_iter()
    }
}

pub fn search_prelude_file(pathseg: &racer::PathSegment, search_type: SearchType,
                           namespace: Namespace) -> vec::IntoIter<Match> {
    debug!("search_prelude file {:?} {:?} {:?}", pathseg, search_type, namespace);
//    debug!("PHIL searching prelude file, backtrace: {}",util::get_backtrace());

    // find the prelude file from the search path and scan it
    let srcpaths = match std::env::var("RUST_SRC_PATH") {
        Ok(paths) => paths,
        Err(_) => return Vec::new().into_iter()
    };

    srcpaths.split(PATH_SEP).filter_map(|srcpath| {
        let filepath = Path::new(srcpath).join("libstd").join("prelude").join("v1.rs");
        if File::open(&filepath).is_ok() { Some(filepath) } else { None} 
    }).flat_map(|filepath| {
        let m = Match::no_comments(pathseg.name.clone(), filepath, 0, true, Undef, "");
        search_scope(&m, 0, search_type, namespace)
    }).collect::<Vec<_>>().into_iter()
}

pub fn resolve_path_with_str(path: &racer::Path, filepath: &Path, pos: usize,
                             search_type: SearchType, namespace: Namespace) 
        -> vec::IntoIter<Match> {

    debug!("resolve_path_with_str {:?}", path);

    // HACK
    let mut matches = if path.segments.len() == 1 && path.segments[0].name == "str" {
        debug!("{:?} == {:?}", path.segments[0], "str");
        let str_pathseg = racer::PathSegment::new("Str");
        let str_match = resolve_name(&str_pathseg, filepath, pos, ExactMatch, namespace).next();
        debug!("str_match {:?}", str_match);

        str_match.map_or(Vec::new(), |str_match| {
            debug!("found Str, converting to str");
            let mut m = str_match.clone();
            m.matchstr = "str".to_string();
            m.local = false;
            m.mtype = Struct;
            m.contextstr = m.matchstr.clone();
            vec![m]
        }).into_iter()
    } else {
        resolve_path(path, filepath, pos, search_type, namespace)
    };

    match search_type {
        ExactMatch => matches.next().map_or(Vec::new(), |m| vec![m]).into_iter(),
        StartsWith => matches
    }
}

thread_local!(pub static SEARCH_STACK: Vec<Search> = Vec::new());

#[derive(PartialEq,Debug)]
pub struct Search {
    path: Vec<String>,
    filepath: String,
    pos: usize
}

pub fn is_a_repeat_search(new_search: &Search) -> bool {
    SEARCH_STACK.with(|v| v.iter().any(|s| s == new_search))
}

fn resolve_name(pathseg: &racer::PathSegment, filepath: &Path, pos: usize,
                    search_type: SearchType, namespace: Namespace) -> vec::IntoIter<Match> {
    let mut out = Vec::new();
    let searchstr = &pathseg.name;

    debug!("resolve_name {} {:?} {} {:?} {:?}", searchstr, filepath.to_str(), 
                                                pos, search_type, namespace);

    let mut m = Match::no_comments((*searchstr).clone(), filepath, pos, false, Undef, "");

    let is_std = match search_type {
        ExactMatch => searchstr == "std",
        StartsWith => "std".starts_with(searchstr)
    };

    if is_std {
        if let Some(ref crate_path) = get_crate_file("std", filepath) {
            let ctxt = crate_path.to_str().unwrap();
            out.push(Match::new("std", crate_path, 0, false, Module, ctxt));
            if let ExactMatch = search_type {
                return out.into_iter();
            }
        }
    }

    let mut searches = search_local_scopes(&mut m, search_type, namespace)
                      .chain(search_crate_root(pathseg, filepath, search_type, namespace))
                      .chain(search_prelude_file(pathseg, search_type, namespace));

    match search_type {
        ExactMatch => if let Some(m) = searches.next() { out.push(m); },
        StartsWith => out.extend(searches.chain(
            do_file_search(searchstr, &filepath.parent().unwrap())))
    }

    out.into_iter()
}

// Get the scope corresponding to super::
pub fn get_super_scope(filepath: &Path, pos: usize) -> Option<racer::Scope> {

    let msrc = racer::load_file_and_mask_comments(filepath);
    let mut path = scopes::get_local_module_path(&msrc, pos);

    if path.is_empty() {
        let filepath = filepath.parent().unwrap();  // safe because file is valid
        ["mod.rs", "lib.rs"].into_iter()
                            .map(|f| filepath.join(f))
                            .find(|f| path_exists(f))
                            .map(|f| racer::Scope::new(f, 0))
    } else if path.len() == 1 {
        Some(racer::Scope::new( filepath.to_owned(), 0))
    } else {
        path.pop();
        let path = racer::Path::from_vec(false, path);
        debug!("get_super_scope looking for local scope {:?}", path);
        resolve_path(&path, filepath, 0, SearchType::ExactMatch, Namespace::TypeNamespace)
            .next()
            .and_then(|m| msrc[m.point..]
                .find('{')
                .map(|p| racer::Scope::new(filepath.to_owned(),m.point + p + 1 )))
    }
}

pub fn resolve_path(path: &racer::Path, filepath: &Path, pos: usize,
                    search_type: SearchType, namespace: Namespace) 
        -> vec::IntoIter<Match> {

    debug!("resolve_path {:?} {:?} {} {:?}", path, filepath.to_str(), pos, search_type);
    
    match path.segments.len() {
        // TODO: Should this better be an assertion ? Why do we have a racer::Path
        // with empty segments in the first place ?
        0   => Vec::new().into_iter(),
        1   => resolve_name(&path.segments[0], filepath, pos, search_type, namespace),
        len => {
            match &*path.segments[0].name {
                "self" => {
                    let mut newpath: racer::Path = path.clone();
                    newpath.segments.remove(0);
                    resolve_path(&newpath, filepath, pos, search_type, namespace)
                }
                "super" => {
                    get_super_scope(filepath, pos)
                    .map_or(Vec::new().into_iter(), |scope| {
                        debug!("PHIL super scope is {:?}", scope);

                        let mut newpath: racer::Path = path.clone();
                        newpath.segments.remove(0);
                        resolve_path(&newpath, &scope.filepath,
                                     scope.point, search_type, namespace)
                    })
                }
                _ => {
                    let mut parent_path: racer::Path = path.clone();
                    parent_path.segments.pop();          
                    let ref pathseg = path.segments[len-1];
                    resolve_path(&parent_path, filepath, pos, ExactMatch, TypeNamespace).next()
                    .map_or(Vec::new().into_iter(), |m| {
                        match m.mtype {
                            Module => {
                                let mut mmodule = m.clone();
                                mmodule.matchstr = pathseg.name.clone();
                                mmodule.local = false;
                                debug!("searching a module '{}' (whole path: {:?})", m.matchstr, path);
                                search_next_scope(&mut mmodule, search_type, namespace)
                            }
                            Enum => {
                                debug!("searching an enum '{}' (whole path: {:?}) searchtype: {:?}", m.matchstr, path, search_type);
                                let filesrc = racer::load_file(&m.filepath);
                                let scopestart = scopes::find_stmt_start(&*filesrc, m.point).unwrap();
                                codeiter::iter_stmts(&filesrc[scopestart..]).next()
                                    .map_or(Vec::new().into_iter(), |(blobstart, blobend)|
                                        matchers::match_enum_variants(&*filesrc,
                                                                      scopestart + blobstart, 
                                                                      scopestart + blobend,
                                                                      &*pathseg.name, 
                                                                      &m.filepath, 
                                                                      search_type, true))
                            }
                            Struct => {
                                debug!("found a struct. Now need to look for impl");
                                ImplIter::new(&m, false).flat_map(|m| {
                                    debug!("found impl!! {:?}", m);
                                    let mut mimpl = m.clone();
                                    mimpl.matchstr = pathseg.name.clone();

                                    // find the opening brace and skip to it.
                                    (&m.src[m.point..]).find('{')
                                    .map_or(Vec::new().into_iter(), |n| {
                                        mimpl.point += n + 1;
                                        search_scope(&mimpl, mimpl.point, search_type, namespace)
                                    })
                                }).collect::<Vec<_>>().into_iter()
                            }
                            _ => Vec::new().into_iter()
                        }
                    })
                }
            }
        }
    }
}

pub fn do_external_search(path: &[&str], filepath: &Path, pos: usize, 
                          search_type: SearchType, namespace: Namespace) 
        -> vec::IntoIter<Match> {

    debug!("do_external_search path {:?} {:?}", path, filepath.to_str());
    if path.len() == 1 {

        let searchstr = path[0];
        let mut m = Match::new(searchstr, filepath, pos, false, Undef, "");

        // hack for now
        // let pathseg = racer::PathSegment::new(searchstr);
        let mut out = search_next_scope(&mut m, search_type, namespace).collect::<Vec<_>>();

        get_module_file(searchstr, &filepath.parent().unwrap()).map(|path| {
            out.push(Match::new(searchstr, &path, 0, false, Module, path.to_str().unwrap()));
        });
        out.into_iter()

    } else {
        let parent_path = &path[..(path.len()-1)];
        do_external_search(parent_path, filepath, pos, ExactMatch, TypeNamespace).next()
        .map_or(Vec::new().into_iter(), |m| {
            match m.mtype {
                Module => {
                    debug!("found an external module {}", m.matchstr);
                    let mut mclone = m.clone();
                    mclone.matchstr = path[path.len()-1].to_string();
                    mclone.local = false;
                    search_next_scope(&mut mclone, search_type, namespace)
                }
                Struct => {
                    debug!("found a pub struct. Now need to look for impl");
                    ImplIter::new(&m, false)
                    .flat_map(|m| {
                        debug!("found  impl2!! {}", m.matchstr);
                        let mut mclone = m.clone();
                        mclone.matchstr = path[path.len()-1].to_string();
                        mclone.local = false;
                        debug!("about to search impl scope...");
                        search_next_scope(&mut mclone, search_type, namespace)
                    }).collect::<Vec<_>>().into_iter()
                }
                _ => Vec::new().into_iter()
            }
        })
    }
}

pub fn search_for_field_or_method<'a>(context: &'a Match, searchstr: &'a str, 
                                      search_type: SearchType) 
        -> Box<Iterator<Item=Match> + 'a> {
    let m = context;
    match m.mtype {
        Struct => {
            debug!("got a struct, looking for fields and impl methods!! {}", m.matchstr);
            Box::new(search_struct_fields(searchstr, &m, search_type)
            .chain(search_for_impl_methods(&m, searchstr, search_type))) 
            as Box<Iterator<Item=Match> + 'a>
        },
        Enum => {
            debug!("got an enum, looking for impl methods {}", m.matchstr);
            Box::new(search_for_impl_methods(&m,searchstr, search_type)) 
            as Box<Iterator<Item=Match> + 'a>
        },
        Trait => {
            debug!("got a trait, looking for methods {}", m.matchstr);
            // search_scope_for_methods(&m, searchstr, search_type)
            Box::new(MethodIter::new(&m, searchstr, search_type)) 
            as Box<Iterator<Item=Match> + 'a>
        }
        _ => { 
            debug!("WARN!! context wasn't a Struct, Enum or Trait {:?}",m);
            Box::new(Vec::<Match>::new().into_iter()) as Box<Iterator<Item=Match> + 'a>
        }
    }
}
