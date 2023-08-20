# A Style Guide for writing Idris Code

This is the coding style I try to adhere to in my Idris project. Older
projects might still use a variety of other styles but I'm working on
transferring them all to the style presented here.

This is loosely based on
[Johan Tibell's Haskell Style Guide](https://github.com/tibbe/haskell-style-guide)

## Formatting

### Line Length

Maximum line length is 80 characters.

### Indentation

Do not use Tabs for indenting but use spaces everywhere. Use 2 spaces for
indenting code blocks. In general, layout your code in such a way that
indentation is minimal without violating the maximum line length.

```idris
module README

import Data.String

hello : IO ()
hello = do
  putStr "Please enter your name: "
  name <- map trim getLine
  putStrLn "Hello \{name}."
```

### Blank Lines

Use blank lines (typically one blank line, but more is OK if it helps
readability) to separate top-level definitions. Do not add a blank line
between function declarations and function definitions:

```idris
twice : Num a => a -> a
twice = (2 *)

square : Num a => a -> a
square x = x * x
```

### White Space

Consider aligning the arrows in case and do blocks,
the colons in data declarations, and the equals signs in function
implementations if it helps readability. This is not mandatory
as it can lead to larger git diffs when renaming stuff, but
I still often do it.

Aligning `case` blocks:

```idris
nucleobase : String -> Maybe String
nucleobase s = case toLower s of
  "adenine"  => Just "A"
  "guanine"  => Just "G"
  "thymine"  => Just "T"
  "cytosine" => Just "C"
  _          => Nothing
```

Aligning `do` blocks:

```idris
readAndAdd : IO ()
readAndAdd = do
  valX <- map trim getLine
  y    <- map trim getLine
  vz   <- map trim getLine
  printLn (cast {to = Nat} valX + cast y + cast vz)
```

Aligning function definitions:

```idris
myNot : Bool -> Bool
myNot True  = False
myNot False = True
```

Aligning data constructors:

```idris
data Something : Type where
  SomeX         : Nat -> Something
  SomethingElse : String -> Something
  Nothing       : Something
```

Aligning record fields:

```idris
record User where
  constructor MkUser
  id        : Nat
  firstName : String
  lastName  : String
  age       : Nat
  password  : String
```

### Data Declarations

Prefer records over single-constructor data declarations whenever possible:

```idris
record Prog a where
  constructor MkProg
  run : String -> IO (Either String a)
```

Use GADT-style data declarations for everything else except plain
enumerations:

```idris
data Error : Type -> Type where
  Custom     : (err : e) -> Error e
  Message    : (msg : String) -> Error e
  EndOfInput : Error e
```

This is fine:

```idris
data YesNo = Yes | No
```

This is also fine:

```idris
data YN : Type where
  N : YN
  Y : YN
```

### List Declarations

Align the values in lengthy list declarations starting on a new line:

```idris
fibonacci : List Nat
fibonacci =
  [ 1
  , 1
  , 2
  , 3
  , 5
  , 8
  , 13
  , 21
  , 34
  , 55
  , 89
  ]
```

### Case Expressions

Consider starting a case blocks on a new line when it helps
readability:

```idris
printValues : List Ordering -> IO ()
printValues vs =
  for_ vs $ \x =>
    case x of
      LT => putStrLn "less than"
      GT => putStrLn "greater than"
      EQ => printLn 0
```

The above could also be written with lambda-case syntax:

```idris
printValues' : List Ordering -> IO ()
printValues' vs =
  for_ vs $ \case
    LT => putStrLn "less than"
    GT => putStrLn "greater than"
    EQ => printLn 0
```

For non-nested case blocks it's also OK to start them on the current line:

```idris
orderNr : String -> Maybe Nat
orderNr s = case toLower s of
  "h"  => Just 1
  "he" => Just 2
  "li" => Just 3
  "be" => Just 4
  "b"  => Just 5
  "c"  => Just 6
  _    => Nothing
```

## Function Declarations

Prefer named arguments over unnamed ones especially when there
are several arguments of the same type:

```idris
login : (name : String) -> (password : String) -> Bool
```

It is fine to group named arguments of the same type:

```idris
login' : (name, password : String) -> Bool
```

If a function declaration does not fit on a single line, align
its arguments on the following lines in the style shown below:

```idris
lengthyFunctionDecl:
     (arg1       : String)
  -> (anotherArg : Nat)
  -> (keep       : Bool)
  -> Either String (List Nat)
```

In case of auto-implicit arguments, using `{auto _ : Foo}` syntax
in multi-line function declarations instead of interface arrows (`=>`)
is mandatory, because it greatly enhances readability:

```idris
programm:
     {auto _   : HasIO io}
  -> {auto _   : Eq t}
  -> (numLines : Nat)
  -> (keep     : t -> Bool)
  -> io (Either String (List t))
```

## Comments

Write documentation for all exported top-level functions, interfaces
and data types.

<!-- vi: filetype=idris2:syntax=markdown
-->
