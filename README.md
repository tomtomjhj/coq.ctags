# `coq.ctags`
`coq.ctags` is a [Universal Ctags][u-ctags] configuration (["optlib parser"][optlib]) for Coq.

## Features
* Supports many built-in commands that define some identifiers.
* Supports unicode identifiers.
* Doesn't get confused by string, comments, attributes, etc.

### Not supported (yet)
* `Axiom`, `Conjecture`, `Parameter`, `Hypothesis`, `Variable`
* `Theorem ... with`, `Record ... with` (`Inductive ... with` and `Fixpoint ... with` are supported)
* Automatically generated identifiers
    * `Build_XXX`
    * `XXX_ind`, ...
* [`constructors_or_record`](https://coq.inria.fr/refman/language/core/inductive.html#grammar-token-constructors_or_record)
* Notations
    * [basic notation](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#coq:cmd.Notation)
    * [abbreviation](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#coq:cmd.Notation-(abbreviation))
    * [tactic notation](https://coq.inria.fr/refman/user-extensions/syntax-extensions.html#coq:cmd.Tactic-Notation)
* ... ?

### Caveat
* Assumes that parentheses/braces/brackets in terms are well-balanced.
* Notations that contain `;` confuses record field parsing. This results in some unwanted tag entries.

## Requirements
A recent version of [Universal Ctags](u-ctags) with `+pcre2` feature is required.

```console
$ ctags --list-features
#NAME             DESCRIPTION
...
pcre2             has pcre2 regex engine
...
```

## Usage
```consol
$ ctags --options=/path/to/coq.ctags [options] [file(s)]
```

Some notable `[options]`:
* `-R`: Recurse into directories
* `-e`: Output `TAGS` file for Emacs

Please see [`ctags(1)`](https://docs.ctags.io/en/latest/man/ctags.1.html) for more details.

Example usage with [`fd`](https://github.com/sharkdp/fd):
```console
$ fd -e v -X ctags --options=/path/to/coq.ctags
```

## Implementation
`coq.ctags` uses some experimental features of Universal Ctags.
* [PCRE2](https://docs.ctags.io/en/latest/optlib.html#perl-compatible-regular-expressions-pcre2-engine)
* [Multiple regex table](https://docs.ctags.io/en/latest/optlib.html#advanced-pattern-matching-with-multiple-regex-tables)
* (Not used yet, but would be necessary for adding support for more Coq features) [Optscript](https://docs.ctags.io/en/latest/optscript.html)

## Related work
* [`etags` configuration from HoTT project](https://github.com/HoTT/HoTT/blob/63b231362bc9ea91112ee53c624d6eb13c36eab6/Makefile.coq.local#L290-L296)
* [`coqtags` Perl script from Proof General](https://github.com/ProofGeneral/PG/blob/master/coq/coqtags)
* `coqdoc` uses `.glob` files to generate hyperlinks.

[u-ctags]: https://github.com/universal-ctags/ctags
[optlib]: https://docs.ctags.io/en/latest/optlib.html
