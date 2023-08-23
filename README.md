# A Style Guide for writing Idris Code

This is the coding style I try to adhere to in my Idris projects. Older
projects might still use a variety of other styles but I'm working on
transferring them all to the style presented here.

This is loosely based on
[Johan Tibell's Haskell Style Guide](https://github.com/tibbe/haskell-style-guide)

## Formatting

### Line Length

Maximum line length is 80 characters. In general, if an expression exceeds
the maximum line length, it should be moved to the next line, indented by
two spaces, and split onto several lines as shown in detail below.

### Indentation

Do not use Tabs for indenting but use spaces everywhere. Use 2 spaces for
indenting code blocks. In general, layout your code in such a way that
indentation is minimal without violating the maximum line length.

```idris
module README

import Data.IORef
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
nucleobase s =
  case toLower s of
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

Start a case block on a new line indented by two characters for
improved readability:

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
  for_ vs $
    \case
      LT => putStrLn "less than"
      GT => putStrLn "greater than"
      EQ => printLn 0
```

Another example:

```idris
orderNr : String -> Maybe Nat
orderNr s =
  case toLower s of
    "h"  => Just 1
    "he" => Just 2
    "li" => Just 3
    "be" => Just 4
    "b"  => Just 5
    "c"  => Just 6
    _    => Nothing
```

If the right-hand side of an arrow in a case block is too long,
begin a new line, indent by two, and split everything across several
lines:

```idris
describeVals : (x,y : Nat) -> String
describeVals x y =
  case compare x y of
    LT =>
      """
      x: \{show x}
      y: \{show x}
      x is less than y
      """
    EQ =>
      """
      x: \{show x}
      y: \{show x}
      x is equal to y
      """
    GT =>
      """
      x: \{show x}
      y: \{show x}
      x is greater than y
      """
```

### Let Expressions

Use `:=` instead of the overloaded `=` in let expressions. Also,
indent the `let` keyword by two spaces and the `in` keyword by three:

```idris
addSquares : Num a => (x,y : a) -> a
addSquares x y =
  let sx := x * x
      sy := y * y
   in sx + sy
```

Short `let` expressions can also be written on a single line:

```idris
squareInc : Num a => a -> a
squareInc x = let sx := x + 1 in sx * sx
```

As with `case` blocks: If the right-hand side of a variable assignment
is too long, move to the next line, indent by two spaces (relative
to the variable's name) and split across several lines:

```idris
lengthyLet : (x,y,z : Nat) -> Nat
lengthyLet x y z =
  let foo :=
        if x < y || z * z > y || y == 0
           then z * (y + x)
           else 2 * x + z
   in foo * foo
```

### Where Blocks

Function definitions in a `where` block should follow on the next line
indented by two spaces. Consider adding a blank line before the `where`
keyword for enhanced readability:

```idris
sumSquares : Num a => List a -> a
sumSquares = foldl acc 0

  where
    acc : a -> a -> a
    acc sum v = sum + v * v
```

### Function Declarations

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

In case of auto-implicit arguments, using `{auto _ : Foo}` syntax (with
an underscore for the name or an explicit name)
in multi-line function declarations instead of interface arrows (`=>`)
is mandatory, because it greatly enhances readability:

```idris
programm:
     {auto _   : HasIO io}
  -> {auto eq  : Eq t}
  -> (numLines : Nat)
  -> (keep     : t -> Bool)
  -> io (Either String (List t))
```

### Function Application

When a function application exceeds the line limit, move to the next
line, indent by two spaces, and list every argument on its own line,
again indented by two spaces:

```idris
record Person where
  constructor MkPerson
  name    : String
  age     : Nat
  hobbies : List String

me : Person
me =
  MkPerson
    "Stefan Höck"
    45
    [ "writing Idris style guides"
    , "family"
    , "playing (classical) guitar"
    , "hiking"
    ]
```

In case of functions with named arguments (such as `MkPerson`
above), consider using named arguments during function application
as well. The code will become much clearer, and changing the order
of arguments in a function definition will not affect your
function application:

```idris
meAgain : Person
meAgain =
  MkPerson
    { name    = "Stefan Höck"
    , age     = 45
    , hobbies =
        [ "writing Idris style guides"
        , "family"
        , "playing (classical) guitar"
        , "hiking"
        ]
    }
```

### Idiom Brackets

When the function application in a pair of idiom brackets exceeds the
preferred line length, proceed as with function application in general
and put the closing idiom brackets on their own line:

```idris
nameM : Maybe String
nameM = Nothing

ageM : Maybe Nat
ageM = Nothing

maybeMe : Maybe Person
maybeMe =
  [| MkPerson
       nameM
       ageM
       (Just ["writing Idris style guides", "family", "head banging"])
  |]
```

### `do` blocks

Always start `do` blocks on a new line indented by two spaces with
the `do` keyword being the last token on the previous line:

```idris
myProg : IO ()
myProg = do
  putStr "Please enter a natural number: "
  s1 <- map trim getLine
  case cast {to = Nat} s1 of
    0 => putStrLn "Not going to read any more numbers."
    n => do
      ref <- newIORef Z
      putStrLn "Reading \{show n} numbers now:"

      for_ [1..n] $ \i => do
        putStr "Enter number \{show i}: "
        s <- map trim getLine
        modifyIORef ref $ (+ cast s)

      val <- readIORef ref
      putStrLn "Total sum is \{show val}"
```

## Comments

Write documentation for all exported top-level functions, interfaces
and data types.

This is probably the most important rule in this style guide, and the one
I too often neglect myself. Documentation is of uttermost important
and writing clear, concise documentation is very hard.

## Mutually recursive Functions

Avoid `mutual` blocks and prefer declaring mutually recursive
functions before writing their definitions:

```idris
even : Nat -> Bool

odd : Nat -> Bool

even 0     = True
even (S k) = not (odd k)

odd 0     = False
odd (S k) = not (even k)
```

This also works for mutually recursive data types:

```idris
data Forest : Type -> Type

data Tree : Type -> Type

data Forest where
  Nil  : Forest a
  (::) : Tree a -> Forest a -> Forest a

data Tree where
  Leaf   : (val : a) -> Tree a
  Branch : (val : a) -> (children : Forest a) -> Tree a
```

## Parameters Blocks

In order to reduce the length of function declarations sharing
one or more read-only arguments (parameters), consider using a
`parameters` block. This works especially well with auto-implicit
arguments:

```idris
parameters {auto _ : HasIO io}
           {auto _ : Num t}
           {auto _ : Ord t}
           {auto _ : Neg t}
           {auto _ : Show t}

  printAbs : t -> io ()
  printAbs v = if v < 0 then printLn (negate v) else printLn v

  printDiff : t -> t -> io () 
  printDiff x y = printAbs (x - y)
```

This style is also well suited for injecting dependencies into
functions by means of auto-implicit arguments. I strongly prefer this over
using the `ReaderT` monad transformer.

Here is an example skeleton application demonstrating this. We annotate
our auto implicit utilities with `[noHints]` to make sure Idris2 does
not come up with some unexpected and nonsensical default value during
proof search:

```idris
data LogLevel = Debug | Info | Warn | Err

record Logger where
  [noHints]
  constructor MkLogger
  log : LogLevel -> Lazy String -> IO ()

emptyLogger : Logger
emptyLogger = MkLogger $ \_,_ => pure ()

record Config where
  [noHints]
  constructor MkConfig
  numberOfThreads : Nat
  maxLineLength   : Nat
  maxFileSize     : Nat
  useColor        : Bool
  caseSensitive   : Bool

defltConfig : Config
defltConfig =
  MkConfig
    { numberOfThreads = 1
    , maxLineLength   = 80
    , maxFileSize     = 1_000_000_000
    , useColor        = False
    , caseSensitive   = True
    }

parameters {auto conf : Config}
           {auto log  : Logger}

  utility : IO Nat

  program : IO ()

main : IO ()
main =
  program
    { conf = defltConfig
    , log  = emptyLogger
    }
```

## Interfaces

These notes are especially important for people coming from Haskell.

Idris is not Haskell and interfaces are not type classes although there
are several interfaces in the core libraries with corresponding Haskell
type classes.

That said, think twice before defining your own interface. Even though
there might be a corresponding type class in Haskell, you may not need it.
Idris supports overloaded function names without the need of using an
interface. Also, interface resolution is just a special case of
proof search, and as such, many programming patterns that can only be
implemented with a type class in Haskell are more naturally written
with predicates and proof search in Idris.

Finally, interfaces in Idris are first-class: You can write
an implementation manually and pass it around explicitly:

```idris
myEq : Eq Bool
myEq = MkEq (\_,_ => False) (\_,_ => True)

test : Bool -> Bool -> Bool
test = (==) @{myEq}
```
<!-- vi: filetype=idris2:syntax=markdown
-->
