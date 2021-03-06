
module WHILE-1op where

open import Agda.Builtin.Nat using (Nat)
open import WHILE using (π»)

-- Definition 3.7.5 --

data Expression : Set where
    var : Nat β Expression
    atom : π» β Expression
    nil : Expression
    cons-var_var_ : Nat β Nat β Expression
    hd-var_ tl-var_ : Nat β Expression
    var_=?var_ : Nat β Nat β Expression

data Command : Set where
    var_:=_ : Nat β Expression β Command
    _Β»_ : Command β Command β Command
    while-var_begin_end : Nat β Command β Command
infix 21 var_:=_
infixl 20 _Β»_

data Program : Set where
    read-to-var_Β»_Β»write-from-var_ : Nat β Command β Nat β Program

infix 19 read-to-var_Β»_Β»write-from-var_

