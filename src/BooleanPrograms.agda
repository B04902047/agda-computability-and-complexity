
open import Agda.Builtin.Nat using (Nat)
open import Data.List using
    ( List
    ; []
    ; _∷_
    )

data Instructions : Set where
    X_:=true : Nat → Instructions
    X_:=X_and-X_ : Nat → Nat → Nat → Instructions
    X_:=not-X_ : Nat → Nat → Instructions

data Programs : Set where
    read-to-X0-»_»-write-from-X0 : List Instructions → Programs

open import WHILE using
    ( 𝔻
    ; numerals
    ; nil
    ; _·_
    )

:=true : 𝔻
:=true = ((nil · nil) · nil)

:=and : 𝔻
:=and = ((nil · nil) · (nil · nil))

:=not : 𝔻
:=not = (((nil · nil) · nil) · (nil · nil))

instruction-to-𝔻 : Instructions → 𝔻
instruction-to-𝔻 (X i :=true) = (:=true · (numerals i) · nil)
instruction-to-𝔻 (X i :=X j and-X k) = (:=and · (numerals i) · (numerals j) · (numerals k) · nil)
instruction-to-𝔻 (X i :=not-X j) = (:=not · (numerals i) · (numerals j) · nil)

programs-to-𝔻 : Programs → 𝔻
programs-to-𝔻 (read-to-X0-» [] »-write-from-X0) = nil
programs-to-𝔻 (read-to-X0-» (I ∷ Is) »-write-from-X0) = (instruction-to-𝔻 I) · (programs-to-𝔻 (read-to-X0-» Is »-write-from-X0))
