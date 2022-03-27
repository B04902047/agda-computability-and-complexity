
module WHILE-1op where

open import Agda.Builtin.Nat using (Nat)
open import WHILE using (𝔻)

-- Definition 3.7.5 --

data Expression : Set where
    var : Nat → Expression
    atom : 𝔻 → Expression
    nil : Expression
    cons-var_var_ : Nat → Nat → Expression
    hd-var_ tl-var_ : Nat → Expression
    var_=?var_ : Nat → Nat → Expression

data Command : Set where
    var_:=_ : Nat → Expression → Command
    _»_ : Command → Command → Command
    while-var_begin_end : Nat → Command → Command
infix 21 var_:=_
infixl 20 _»_

data Program : Set where
    read-to-var_»_»write-from-var_ : Nat → Command → Nat → Program

infix 19 read-to-var_»_»write-from-var_

