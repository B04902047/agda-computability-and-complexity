
open import Agda.Builtin.Nat

open import I renaming (
      Expression to I-expression
    ; Command to I-command
    ; Program to I-program
    )

open import WHILE renaming
    ( Expression to WHILE-expression
    ; Command to WHILE-command
    ; Program to WHILE-program
    )


-- Figure 3.6. --

WHILE-to-I-expression : WHILE-expression → I-expression
WHILE-to-I-expression (var i) = hd ((tl^ i) A)
WHILE-to-I-expression nil = nil
WHILE-to-I-expression (atom d) = atom d
WHILE-to-I-expression (cons E F) = cons (WHILE-to-I-expression E) (WHILE-to-I-expression F)
WHILE-to-I-expression (hd E) = hd (WHILE-to-I-expression E)
WHILE-to-I-expression (tl E) = tl (WHILE-to-I-expression E)
WHILE-to-I-expression (E =? F) = (WHILE-to-I-expression E) =? (WHILE-to-I-expression F)

init-X-in-A : Nat → I-expression
init-X-in-A 0       = cons A nil
init-X-in-A (suc n) = cons nil (init-X-in-A n)

open import Data.Bool using () renaming
    ( if_then_else_ to ifᵇ_then_else_
    )

assign_to_in-A-with-max : I-expression → Nat → Nat → I-expression
assign E to X in-A-with-max 0
    = cons varX' nil
    where varX' = ifᵇ (X == 0)
                    then E
                    else (WHILE-to-I-expression (var 0))
assign E to X in-A-with-max (suc n)
    = cons varX' (assign E to X in-A-with-max n)
    where varX' = ifᵇ ((suc n) == X)
                    then E
                    else (WHILE-to-I-expression (var n))

WHILE-to-I-command : WHILE-command → Nat → I-command
WHILE-to-I-command (var X := E )         max-var = A:= (assign E' to X in-A-with-max max-var)
    where E' = WHILE-to-I-expression E
WHILE-to-I-command (C1 » C2)             max-var = C1' » C2'
    where C1' = WHILE-to-I-command C1 max-var
          C2' = WHILE-to-I-command C2 max-var
WHILE-to-I-command (while E begin C end) max-var = while E' begin C' end
    where E' = WHILE-to-I-expression E
          C' = WHILE-to-I-command C max-var

max : Nat → Nat → Nat
max zero    n       = n
max m       zero    = m
max (suc m) (suc n) = suc (max m n)

max-var-in-expression : WHILE-expression → Nat
max-var-in-expression (var i) = i
max-var-in-expression nil = 0
max-var-in-expression (atom d) = 0
max-var-in-expression (cons E F) = max (max-var-in-expression E) (max-var-in-expression F)
max-var-in-expression (hd E) = max-var-in-expression E
max-var-in-expression (tl E) = max-var-in-expression E
max-var-in-expression (E =? F) = max (max-var-in-expression E) (max-var-in-expression F)

max-var-in-command : WHILE-command → Nat
max-var-in-command (var i := E ) = max i (max-var-in-expression E) 
max-var-in-command (C1 » C2) = max (max-var-in-command C1) (max-var-in-command C2)
max-var-in-command (while E begin C end) = max (max-var-in-expression E) (max-var-in-command C)

max-var-in-program : WHILE-program → Nat
max-var-in-program (read-var i » C »write-var j) = max (max i j) (max-var-in-command C)

WHILE-to-I-program : WHILE-program → I-program
WHILE-to-I-program (read-var X » C »write-var Y) =
    read-to-A»
        A:= (assign A to X in-A-with-max max-var) »
        C' »
        A:= varY'
    »write-from-A
    where varY' = WHILE-to-I-expression (var Y)
          max-var = max-var-in-program (read-var X » C »write-var Y)
          C' = WHILE-to-I-command C max-var

-- Proposition 3.7.4 --

open import Language using (IsSubset; IsHighLevelCompilingFunction; WHILE; Language)
open import Data.Product using (_,_)


WHILE-isSubsetOf-𝔻 : IsSubset WHILE-program 𝔻
WHILE-isSubsetOf-𝔻 = (IsWhileProgram , (λ p → (program-to-data p , {!   !})) , λ {(d , d-isProgram) → {!   !}})
    where IsWhileProgram : 𝔻 → Set
          IsWhileProgram = {!   !}

postulate
    I : Language I-program 𝔻
    I-isSubsetOf-𝔻 : IsSubset I-program 𝔻

prop-3-7-4 : IsHighLevelCompilingFunction {𝔻} {WHILE-program} {I-program}
                WHILE-to-I-program WHILE I
prop-3-7-4 {p@(read-var X » C »write-var Y)} {d} {e} = {!   !}
    where [_]ᴵ_≃_ = Language.[_]_≃_ I
          [_]ᵂᴴᴵᴸᴱ_≃_ = Language.[_]_≃_ WHILE
          only-if-direction : ([ p ]ᵂᴴᴵᴸᴱ d ≃ e) → ([ (WHILE-to-I-program p) ]ᴵ d ≃ e)
          only-if-direction (σ , C⊢σ₀⇒σ , σY≡e)
              with C⊢σ₀⇒σ
          ...    | assign {E} {X} {σ} = {!   !}
          ...    | compose C D = {!   !}
          ...    | loop-true isNil C next = {!   !}
          ...    | loop-false isNotNil = {!   !}
          if-direction : ([ (WHILE-to-I-program p) ]ᴵ d ≃ e) → ([ p ]ᵂᴴᴵᴸᴱ d ≃ e)
          if-direction = {!   !}

-- IsCompilingFunction' : {ST-data S-program T-program L-data : Set}
--                     → IsSubset S-program L-data
--                     → IsSubset T-program L-data
--                     → (f : L-data → L-data)
--                     → (S : Language S-program ST-data)
--                     → (T : Language T-program ST-data)
--                     → Set

open import WHILE-1op renaming
    ( Expression to WHILE¹ᵒᵖ-expression
    ; Command to WHILE¹ᵒᵖ-command
    ; Program to WHILE¹ᵒᵖ-program
    )

-- Figure 3.7 --


-- WHILE-to-WHILE¹ᵒᵖ-command : {Nat} → WHILE-command → WHILE¹ᵒᵖ-command
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := (var Y))    = var Z := var Y
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := nil)        = var Z := nil
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := atom d)     = var Z := atom d
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := (hd E))     = {!   !}
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := (tl E))     = {!   !}
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := (cons E F)) = WHILE-to-WHILE¹ᵒᵖ-command {n + 1} (var n := E)
--                                                     » WHILE-to-WHILE¹ᵒᵖ-command (var (n + 1) := F)
--                                                     » var Z := (cons-var n var (n + 1))
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (var Z := (E =? F))   = {!   !}
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (C1 » C2)             = {!   !}
-- WHILE-to-WHILE¹ᵒᵖ-command {n} (while E begin C end) = {!   !} 