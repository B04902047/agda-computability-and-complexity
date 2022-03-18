
open import Agda.Builtin.Nat

open import I renaming (
      Expressions to I-expressions
    ; Commands to I-commands
    ; Programs to I-programs
    )

open import WHILE renaming
    ( 𝔻 to WHILE-data
    ; Expressions to WHILE-expressions
    ; Commands to WHILE-commands
    ; Programs to WHILE-programs
    )


-- Figure 3.6. --

WHILE-to-I-expression : WHILE-expressions → I-expressions
WHILE-to-I-expression (var i) = hd ((tl^ i) A)
WHILE-to-I-expression nil = nil
WHILE-to-I-expression (cons E F) = cons (WHILE-to-I-expression E) (WHILE-to-I-expression F)
WHILE-to-I-expression (hd E) = hd (WHILE-to-I-expression E)
WHILE-to-I-expression (tl E) = tl (WHILE-to-I-expression E)
WHILE-to-I-expression (E =? F) = (WHILE-to-I-expression E) =? (WHILE-to-I-expression F)

init-X-in-A : Nat → I-expressions
init-X-in-A 0       = cons A nil
init-X-in-A (suc n) = cons nil (init-X-in-A n)

open import Data.Bool using () renaming
    ( if_then_else_ to ifᵇ_then_else_
    )

assign_to_in-A-with-max : I-expressions → Nat → Nat → I-expressions
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

WHILE-to-I-command : WHILE-commands → Nat → I-commands
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

max-var-in-expression : WHILE-expressions → Nat
max-var-in-expression (var i) = i
max-var-in-expression nil = 0
max-var-in-expression (cons E F) = max (max-var-in-expression E) (max-var-in-expression F)
max-var-in-expression (hd E) = max-var-in-expression E
max-var-in-expression (tl E) = max-var-in-expression E
max-var-in-expression (E =? F) = max (max-var-in-expression E) (max-var-in-expression F)

max-var-in-command : WHILE-commands → Nat
max-var-in-command (var i := E ) = max i (max-var-in-expression E) 
max-var-in-command (C1 » C2) = max (max-var-in-command C1) (max-var-in-command C2)
max-var-in-command (while E begin C end) = max (max-var-in-expression E) (max-var-in-command C)

max-var-in-program : WHILE-programs → Nat
max-var-in-program (read-to-var i » C »write-from-var j) = max (max i j) (max-var-in-command C)

WHILE-to-I-program : WHILE-programs → I-programs
WHILE-to-I-program (read-to-var X » C »write-from-var Y) =
    read-to-A»
        A:= (assign A to X in-A-with-max max-var) »
        C' »
        A:= varY'
    »write-from-A
    where varY' = WHILE-to-I-expression (var Y)
          max-var = max-var-in-program (read-to-var X » C »write-from-var Y)
          C' = WHILE-to-I-command C max-var

-- Proposition 3.7.4 --

open import Langauge using (IsCompilingFunction)


-- prop-3-7-4 : IsCompilingFunction {𝔻} 