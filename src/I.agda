
module I where

open import Agda.Builtin.Nat


-- Definition 3.7.1 --

data Expressions : Set where
    A : Expressions
    nil : Expressions
    cons : Expressions → Expressions → Expressions
    hd tl : Expressions → Expressions
    _=?_ : Expressions → Expressions → Expressions

data Commands : Set where
    A:=_ : Expressions → Commands
    _»_ : Commands → Commands → Commands
    while_begin_end : Expressions → Commands → Commands

infix 21 A:=_
infixl 20 _»_

data Programs : Set where
    read-to-A»_»write-from-A : Commands → Programs


-- Example 3.7.2 --

reverse : Programs
reverse =
    read-to-A»
        A:= cons A nil »                                    -- Y <- nil; A <- (X, Y);
        while (hd A) begin                                  -- while (X) {
            A:= cons (hd A) (cons (hd (hd A)) (tl A)) »     --     Y <- cons (hd X) Y;
            A:= cons (tl (hd A)) (tl A)                     --     X <- tl X;
        end »                                               -- }
        A:= tl A                                            -- A <- Y;
    »write-from-A


-- Definition 3.7.3 --

tl^ : Nat → Expressions → Expressions
tl^ zero    E  = E
tl^ (suc n) E = tl ((tl^ n) E)
