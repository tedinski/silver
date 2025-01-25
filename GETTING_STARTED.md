
# Getting Started

This document is intended as an introduction to developing the Silver
system.  It is *not* intended to introduce you to the concepts of
extensible languages or using Silver, only the information you need
for making changes to Silver itself.


For anyone adding to this document:  
Please keep this short.  It is just an introduction for anyone
starting out, and we want them to actually read it.  Any questions
which are too specific to be of general interest can be addressed to
senior students.




## Meta Level and Object Level

One of the difficulties of developing the Silver system is keeping
straight the meta level, the Silver compiler you are working on, and
the object level, the Silver code you are compiling.  For example, if
you are modifying the production for addition, you are writing code
that works on `Expr`s with an attribute called `typerep` with a value
of `intType()` at the meta level; your code is not manipulating
integers, which are at the object level.


As you spend more time working on Silver, you will grow more
accustomed to the difference between the meta and object levels.  When
starting out, you might occasionally need to slow down and think
carefully to ensure you are thinking at the meta level as you work.




## Scripts for Logistics

There are several scripts for building Silver and other logistical
operations in the `silver` repository.


### `deep-rebuild`

The `deep-rebuild` script does several rebuilds of Silver to ensure
that any changes which have been made still permit Silver to build
itself.



### `self-compile`

The `self-compile` script does a simple build of Silver to create a
jar which contains any new changes.  This is faster, but less
rigorous, than `deep-rebuild`.



### `fetch-jars`

This brings in new jar files which have been built by the
continuous-integration server.  Some changes to Silver will require
you to get new jars using this script.  If you have pulled the
`develop` branch and it won't build, run this.



### `deep-clean`

This script cleans out existing generated files.  With no arguments,
it doesn't actually do anything.  Run
```
./deep-clean -delete all
```
to actually clean things.  If your builds are failing and it isn't
because of a change you made, get new jars with `fetch-jars`, clean
with `deep-clean -delete all`, then try rebuilding with
`deep-rebuild`.




## Directory Structure

The code for Silver, other than the runtime, is contained in the
`grammars/silver` directory.



### Standard Library

The standard library is in `grammars/silver/core`.  This includes such
things as basic functions on lists and strings, monads, and basic
types.  It is included in every Silver grammar by default.  If you
need to add some basic type to Silver, or you need to add some kind of
function on basic types, it goes in here.



### Silver's Definition

The host language of Silver is in
`grammars/silver/compiler/definition`.


The `core` directory in this directory is the home of the definitions
of most of the constructs in Silver.  For example, most Silver
host-language expressions are defined in `Expr.sv` here.


Types are defined in the `type` directory under `definition`.  Types
are assigned to expressions in `definition/core`, but type checking to
generate error messages is done in
`grammars/silver/compiler/analysis/typechecking/core`.  This
separation is probably a bad choice, but what is done is done.



### Extensions

Extensions to Silver go in `grammars/silver/compiler/extension`.  Each
extension has its own directory here which contains the code for the
extension.


The extension must also be added to the list of extensions in
`grammars/silver/compiler/host/Project.sv`.  This means it will be
available as part of Silver; without this, it won't be included in
Silver.



### Modifications

Modifications are things which aren't conceptually part of the Silver
host language, but which can't be pure extensions.  For Silver, these
include lambda functions and collection attributes.  They can be found
in `grammars/silver/compiler/modification`.  Rarely should a construct
be added as a modification.




## Making Changes

You should always make a new branch when making changes to Silver.
**Never** make changes directly on the `develop` branch.  Your
branch's name should take one of two forms, depending on what kind of
changes you are making:
* If you are fixing something so it works as intended, your branch's
  name should start with `bugfix/` followed by a descriptive name.
  For example, `bugfix/list-append-crash` would be a branch fixing the
  behavior of appending lists if it sometimes caused Silver to crash.
* If you are adding a new feature to Silver, your branch's name should
  start with `feature/` followed by a descriptive name.  For example,
  `feature/list-subtraction` would be a branch adding the ability to
  write code like `[1, 2] - [1]`.

You can add your branch to the remote Silver repository by
```
git push -u origin <branch>
```


When you are making changes, you should add test cases for them.
These go in the `test` directory, which has more directories in it for
organizing test cases.  Unless there is already another directory for
testing related to what you are working on (e.g. pattern matching
tests go in `test/patt`), it should go in `test/silver_features`.  The
syntax for writing tests is best seen by looking at other test files.




## Helpful Hints

A good way to see where something (e.g. a function) is used in the
Silver code base is to use the following command:
```
grep -r --include="*.sv" "function name"
```
This recursively searches every Silver file under the current
directory for occurrences of `"function name"` and shows the lines
which include it.  It can also be used to find where a nonterminal is
declared:
```
grep -r --include="*.sv" "nonterminal Foo"
```
Because this uses `grep`, you can search by regular expression instead
of plain text as well.

