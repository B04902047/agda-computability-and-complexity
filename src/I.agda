
module I where

open import Agda.Builtin.Nat
open import WHILE using (𝔻)

-- Definition 3.7.1 --

data Expression : Set where
    A : Expression
    nil : Expression
    atom : 𝔻 → Expression
    cons : Expression → Expression → Expression
    hd tl : Expression → Expression
    _=?_ : Expression → Expression → Expression

data Command : Set where
    A:=_ : Expression → Command
    _»_ : Command → Command → Command
    while_begin_end : Expression → Command → Command

infix 21 A:=_
infixl 20 _»_

data Program : Set where
    read-to-A»_»write-from-A : Command → Program


-- Example 3.7.2 --

reverse : Program
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

tl^ : Nat → Expression → Expression
tl^ zero    E  = E
tl^ (suc n) E = tl ((tl^ n) E)
