
open import Agda.Builtin.Nat using (Nat)


-- Definition 3.7.5 --

data Expressions : Set where
    var : Nat → Expressions
    nil : Expressions
    cons-var_-var_ : Nat → Nat → Expressions
    hd-var_ tl-var_ : Nat → Expressions
    var_=?var_ : Nat → Nat → Expressions

data Commands : Set where
    var_:=_ : Nat → Expressions → Commands
    _»_ : Commands → Commands → Commands
    while-var_begin_end : Nat → Commands → Commands
infix 21 var_:=_
infixl 20 _»_

data Programs : Set where
    read-to-var_»_»write-from-var_ : Nat → Commands → Nat → Programs

infix 19 read-to-var_»_»write-from-var_


-- Example 3.7.6 --

