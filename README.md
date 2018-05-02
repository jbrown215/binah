# Binah

## Installation

Binah is intented to work with Yesod projects. To set up Binah, you will need to first install Binah and then
make some modifications to your Yesod project for it to run.

You should have Haskell Stack installed and your Yesod project set up with it.

0. Download and install Liquid Haskell from source

```
git clone --recursive https://github.com/ucsd-progsys/liquidhaskell.git
cd liquidhaskell
stack install
```

1. Download and install Binah
```
git clone https://github.com/jbrown215/binah.git
cd binah
stack install
```

2. If you are on most Linux distributions, you may need to add 3 extra lines to the stack.yaml of your Yesod project
```
ghc-options:
  "yaml": -opta-Wa,-mrelax-relocations=no
  "persistent-sqlite": -opta-Wa,-mrelax-relocations=no
```
## Usage

To use Binah, first create a refined-models file as described in the wiki. The refined-models file can include data invariants
and also policies on the data.

1. Copy BinahLibrary.hs

BinahLibrary.hs is the file that will contain all of the generated safe select, update, and unwrap functions that you
will use in your project. Copy this file from binah/refined-models/resources/BinahLibrary.hs into your project.

2. Run binah

```
binah refined-models
```
This generates two files: models-simple and refined-models.spec. You should use models-simple as your models file for the
project, or copy it into your Models.hs is your don't have a dedicated models file.

Note: You may need to add ~ in front of all the fields as well. i.e.

```
table1
  field1 Typ1
  field2 Typ2
```

becomes

```
table1
  ~field1 Typ1
  ~field2 Typ2
```
this makes the fields lazy, which makes them match up with their Liquid Types.

You should copy models.spec into your Models.hs file, right above the line where you define all your database
entities. Depending on your project settings, this line may look something like this:

```
share [mkPersist sqlSettings, mkMigrate "migrateAll"]
  $(persistFileWith lowerCaseSettings "config/models")
```

3. Run binah -p

```
binah -p refined-models
```
This will output all the accessor, update, and unwrap functions that you will need when doing database queries and
working with their results. Copy the output of this to the bottom of BinahLibrary.hs. You may need to add new imports to
get this to compile.

4. Implement

Implement your database queries using the functions from BinahLibrary.hs. Examples:
```
selectTable [filterTableField EQUAL "foo"] []
refinedUpdate id [TableField =# field]
```

5. Verify!

First, run Liquid Haskell on Models.hs and BinahLibrary.hs.

```
stack exec -- liquid --no-adt --exact-data-con -- higherorder --no-termination -i src src/Models.hs
stack exec -- liquid --no-totality -i src --no-pattern-inline --prune-unsorted src/BinahLibrary.hs
```
Models.hs should fail with an error that states that some of your invariants don't hold. This is expected.
BinahLibrary.hs should say safe.

Next, run Liquid Haskell on all of your Handler files. For example, if you have a handler called Home.hs in src/Handler, you
might run
```
stack exec -- liquid -i src --no-pattern-inline --prune-unsorted src/Handler/Home.hs
```
