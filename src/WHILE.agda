
module WHILE where

open import Agda.Builtin.Nat


open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; subst; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


-- Definition 2.1.1 --

data 𝔻 : Set where
    nil : 𝔻
    _·_ : 𝔻 → 𝔻 → 𝔻

infixr 20 _·_


-- Definition 2.1.2 --

size : 𝔻 → Nat
size nil = 1
size (d₁ · d₂) = size d₁ + size d₂


-- Definition 2.1.3 --

data Expression : Set where
    var : Nat → Expression
    nil : Expression
    atom : 𝔻 → Expression
    cons : Expression → Expression → Expression
    hd tl : Expression → Expression
    _=?_ : Expression → Expression → Expression


data Command : Set where
    var_:=_ : Nat → Expression → Command
    _»_ : Command → Command → Command
    while_begin_end : Expression → Command → Command
infix 21 var_:=_
infixl 20 _»_

data Program : Set where
    read-var_»_»write-var_ : Nat → Command → Nat → Program

infix 19 read-var_»_»write-var_


-- Example 2.1.4 --

reverse : Program
reverse = read-var 0 » (
            var 1 := nil »
                while (var 0) begin
                    (var 1 := (cons (hd (var 0)) (var 1)) »
                    var 0 := (tl (var 0)))
                end
        ) »write-var 1


-- Definition 2.1.5 --

false : Expression
false = nil

falseᴰ : 𝔻
falseᴰ = nil

true : Expression
true = cons nil nil

trueᴰ : 𝔻
trueᴰ = nil · nil


-- Example 2.1.6. --

if_then_ : Expression → Command → {new : Nat} → Command
(if E then C) {new} =
    var new := E »              -- E[new]σ' = σ' new = E
    while (var new) begin
        C
        » (var new := false)
    end

if_then_else_ : Expression → Command → Command → {new1 new2 : Nat} → Command
(if E then C1 else C2) {new1} {new2} =
    (var new1 := E)
    » (var new2 := true)
    » while (var new1) begin
        (var new1 := false)
        » (var new2 := false)
        » C1
    end »
    while (var new2) begin
        (var new2 := false)
        » C2
    end

not : Expression → Expression
not E = (E =? false)

_or_ : Expression → Expression → Expression
E or F = not ((cons E F) =? (cons nil nil))     -- not ((cons E F) =? true)

_and_ : Expression → Expression → Expression
E and F = ((cons (not E) (not F)) =? true)


-- Definition 2.1.7 --

open import Data.List using (
      List
    ; _∷_
    ; []
    )

-- list-representation : 𝔻 → List (𝔻 WHILE-atom)
-- list-representation (nil) = []
-- list-representation (d₁ ∷ d₂) = d₁ ∷ˡ (list-representation d₂)

length : 𝔻 → Nat
length nil = 0
length (d₁ · d₂) = 1 + (length d₂)


-- Definition 2.1.8 --

numerals : Nat → 𝔻
numerals 0 = nil
numerals (suc n) = nil · (numerals n)

succ-one-numeral : Program
succ-one-numeral =
    read-var X
        » var Y := cons nil (var X)
    »write-var Y
    where X = 0
          Y = 1

pred-one-numeral : Program
pred-one-numeral =
    read-var X
        » var Y := tl (var X)
    »write-var Y
    where X = 0
          Y = 1

add-two-numerals : Program
add-two-numerals =
    read-var XY
        » ((var X := hd (var XY))           -- X = first XY
        » (var Y := tl (var XY))            -- Y = second XY
        » while (var X) begin               -- while (X != 0)
            (var Y := cons nil (var Y))     --     Y = Y + 1
            » (var X := tl (var X))         --     X = X - 1
        end)
    »write-var Y
    where XY = 0
          X = 1
          Y = 2

skip : Command
skip = var 0 := var 0

list : List Expression → Expression
list [] = nil
list (E ∷ Es) = cons E (list Es)

cons* : List Expression → Expression
cons* [] = nil
cons* (E ∷ []) = E
cons* (E ∷ Es) = cons E (cons* Es)


addVariablesInExpression : Expression → Nat → Expression
addVariablesInExpression (var X)    n = var (X + n)
addVariablesInExpression nil        n = nil
addVariablesInExpression (atom d)   n = atom d
addVariablesInExpression (cons E F) n = cons E' F'
    where E' = addVariablesInExpression E n
          F' = addVariablesInExpression F n
addVariablesInExpression (hd E)     n = hd E'
    where E' = addVariablesInExpression E n
addVariablesInExpression (tl E)     n = tl E'
    where E' = addVariablesInExpression E n
addVariablesInExpression (E =? F)   n = (E' =? F')
    where E' = addVariablesInExpression E n
          F' = addVariablesInExpression F n

addVariablesInCommand : Command → Nat → Command
addVariablesInCommand (var X := E)          n = var (X + n) := E'
    where E' = addVariablesInExpression E n
addVariablesInCommand (C » D)               n = C' » D'
    where C' = addVariablesInCommand C n
          D' = addVariablesInCommand D n
addVariablesInCommand (while E begin C end) n = while E' begin C' end
    where E' = addVariablesInExpression E n
          C' = addVariablesInCommand C n

-- Inline procedure expansion --

postulate
    getVariablesInCommand : Command → List Nat

initVariables : List Nat → Command
initVariables [] = skip
initVariables (X ∷ Xs) = (var X := nil) » (initVariables Xs)

initVariablesInCommand : Command → Command
initVariablesInCommand C = (initVariables (getVariablesInCommand C))

var_:=_⟨_⟩ : Nat → Program → Expression → {Nat} → Command
var A := (read-var X » C »write-var Y) ⟨ E ⟩ {n} =
    var (X + n) := E
    » initVariablesInCommand C'
    » C'
    » var A := (var (Y + n))
    where C' = addVariablesInCommand C n

-- Example 2.1.9 --

append : Program
append = read-var X » (
            var A := hd (var X)
            » var Y := tl (var X)
            » (var B := reverse ⟨ var A ⟩) {n}
            » while (var B) begin
                var Y := cons (hd (var B)) (var Y)
                » var B := tl (var B)
            end
        ) »write-var Y
        where X = 0
              Y = 1
              A = 2
              B = 3
              n = 4

open import Data.Bool using (Bool; _∧_) renaming
    ( if_then_else_ to ifᵇ_then_else_
    ; _<_ to _<ᵇ_
    ; true to trueᵇ
    ; false to falseᵇ
    )


-- Definition 2.2.1 --

Store : Set
Store = Nat → 𝔻

_[_↦_] : Store → Nat → 𝔻 → Store
(σ [ X ↦ d ]) Y = ifᵇ (X == Y) then d else (σ Y)

double-subst : (σ : Store) → (d e : 𝔻) → (X Y : Nat) → ((σ [ X ↦ d ]) [ X ↦ e ]) Y ≡ (σ [ X ↦ e ]) Y
double-subst σ d e X Y with X == Y 
...                       | trueᵇ = refl
...                       | falseᵇ = refl

initial-store : (p : Program) → 𝔻 → Store
initial-store (read-var X » C »write-var Y) d Z
    = ifᵇ (X == Z) then d else nil

σ₀ : (p : Program) → 𝔻 → Store
σ₀ = initial-store


if-X≡X-then-d-else-e : (X : Nat) → (d e : 𝔻) → (ifᵇ X == X then d else e) ≡ d
if-X≡X-then-d-else-e X d e = claim X refl
    where X≡X→X==X : (X : Nat) → X ≡ X → (X == X) ≡ trueᵇ
          X≡X→X==X 0 refl = refl
          X≡X→X==X (suc n) refl = X≡X→X==X n refl
          claim : (X : Nat) → X ≡ X → (ifᵇ X == X then d else e) ≡ (ifᵇ trueᵇ then d else e)
          claim X refl = cong (λ b → ifᵇ b then d else e) (X≡X→X==X X refl)

subst-proof : (σ : Store) → (X : Nat) → (d : 𝔻) → (σ [ X ↦ d ]) X ≡ d
subst-proof σ X d = if-X≡X-then-d-else-e X d (σ X)

initial-store-proof : (X Y : Nat)
                    → (C : Command)
                    → (d : 𝔻)
                    → (σ₀ (read-var X » C »write-var Y) d) X ≡ d
initial-store-proof X Y C d = if-X≡X-then-d-else-e X d nil


getInputVariable : Program → Nat
getInputVariable (read-var X » C »write-var Y) = X

initial-store-proof' : (p : Program) → (d : 𝔻)
                    → (σ₀ p d) (getInputVariable p) ≡ d
initial-store-proof' (read-var X » C »write-var Y) d = initial-store-proof X Y C d


isEqual : 𝔻 → 𝔻 → Bool
isEqual nil     nil     = trueᵇ
isEqual nil     _       = falseᵇ
isEqual _       nil     = falseᵇ
isEqual (e · f) (g · h) = (isEqual e g) ∧ (isEqual f h)


-- Definition 2.2.2 --

E[_] : Expression → Store → 𝔻
E[ (var X) ] σ = σ X
E[ nil ] σ = nil
E[ atom d ] σ = d
E[ cons E F ] σ = (E[ E ] σ) · (E[ F ] σ)
E[ hd E ] σ with E[ E ] σ
... | e · f = e
... | nil   = nil
E[ tl E ] σ with E[ E ] σ
... | e · f = f
... | nil   = nil
E[ E =? F ] σ with isEqual (E[ E ] σ) (E[ F ] σ)
... | trueᵇ  = nil · nil
... | falseᵇ = nil

eval-input-with-initial-store : (X Y : Nat)
                            → (C : Command)
                            → (d : 𝔻)
                            → (E[ var X ] (σ₀ (read-var X » C »write-var Y) d)) ≡ d
eval-input-with-initial-store = initial-store-proof


-- skip-store-pf : (σ : Store) → (X Y : Nat) → ((σ [ X ↦ (E[ (var X) ] σ) ]) Y) ≡ (σ Y)
-- skip-store-pf σ X Y with X == Y
-- ...                    | trueᵇ = {!   !}
--                                     -- cong σ (X==Y→X≡Y X Y {!   !})
--                         where X==Y→X≡Y : (X Y : Nat) → (X == Y) ≡ trueᵇ → X ≡ Y
--                               X==Y→X≡Y 0        0       X==Y = refl
--                               X==Y→X≡Y (suc n)  (suc m) X==Y = cong suc (X==Y→X≡Y n m X==Y)
--                               claim : {A : Set} → (X Y : Nat) → (f : Nat → A) → (ifᵇ (X == Y) then (f X) else (f Y)) ≡ f Y
--                               claim 0        0       f = refl
--                               claim 0        (suc m) f = refl
--                               claim (suc n)  0       f = refl
--                               claim (suc n)  (suc m) f with (n == m)
--                               ...                        | trueᵇ    = {!   !}     -- f (suc n) ≡ f (suc m) | n ≡ m
--                               ...                        | falseᵇ   = refl
-- ...                    | falseᵇ = refl

 

-- Definition 2.2.3 --

open import Relation.Nullary using (¬_)

-- Definition 2.2.3 --

data _⊢_⇒_ : (C : Command) → (σ σ' : Store) → Set where
    assign : {E : Expression} {X : Nat} {σ : Store}
            → (var X := E) ⊢ σ ⇒ (σ [ X ↦ (E[ E ] σ) ])
    compose : {C D : Command} {σ σ' σ'' : Store}
            → (C ⊢ σ ⇒ σ') → (D ⊢ σ' ⇒ σ'')
            → ((C » D) ⊢ σ ⇒ σ'')
    loop-true : {E : Expression} {C : Command} {σ σ' σ'' : Store}
            → ¬ (E[ E ] σ) ≡ nil → (C ⊢ σ ⇒ σ') → ((while E begin C end) ⊢ σ' ⇒ σ'')
            → ((while E begin C end) ⊢ σ ⇒ σ'')
    loop-false : {E : Expression} {C : Command} {σ : Store}
            → (E[ E ] σ) ≡ nil
            → ((while E begin C end) ⊢ σ ⇒ σ)

open import Data.Product using (Σ-syntax; _×_)


-- Definition 2.2.4 --

[_]_≡ : Program → 𝔻 → 𝔻 → Set
[ p@(read-var X » C »write-var Y) ] d ≡ e
    = Σ[ σ ∈ Store ] ((C ⊢ (σ₀ p d) ⇒ σ) × ((σ Y) ≡ e))

open import Agda.Builtin.Maybe using (Maybe; nothing; just)

open import Level using (Level; _⊔_) renaming (suc to lsuc)

_↔_ : {ℓ₁ ℓ₂ : Level} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A ↔ B = (A → B) × (B → A)

[_]≡ : {ℓ : Level} → Program → (𝔻 → 𝔻 → Set ℓ) → Set ℓ
[ p ]≡ f = (x y : 𝔻) → (f x y) ↔ ([ p ] x ≡ y)

[_]_↓ : Program → 𝔻 → Set
[ p ] d ↓ = Σ[ e ∈ 𝔻 ] ([ p ] d ≡ e)

equality-test : Program
equality-test = read-var X » (
                    (var GO := true)
                    » (var Y := false)
                    » (var D := hd (var X))
                    » (var E := tl (var X))
                    » while (var GO) begin (
                        (if (var D) then (
                            (var D1 := hd (var D))
                            » (var D2 := tl (var D))
                            » ((if (var D1) then (
                                (if (var E) then (
                                    (var E1 := hd (var E))
                                    » (var E2 := tl (var E))
                                    » ((if (var E1) then (
                                            (var D := cons (hd (var D1)) (cons (tl (var D1)) ((var D2))))
                                            » (var E := cons (hd (var E1)) (cons (tl (var E1)) ((var E2))))
                                        ) else (var GO := false)) {temp7} {temp8}
                                    )
                                ) else (var GO := false)) {temp5} {temp6}
                            ) else (
                                (if (var E) then
                                    (if (hd (var E)) then (var GO := false)
                                    else (
                                        (var D := tl (var D))
                                        » (var E := tl (var E))
                                    )) {temp11} {temp12}
                                else (var GO := false)) {temp9} {temp10}
                            )) {temp3} {temp4}
                        )) else (
                            (if (var E) then (var GO := false)
                            else (
                                (var Y := true)
                                » (var GO := false)
                            )) {temp13} {temp14}
                        )) {temp1} {temp2}
                    ) end
                ) »write-var Y
                where X = 0
                      Y = 1
                      GO = 2
                      D = 3
                      D1 = 4
                      D2 = 5
                      E = 6
                      E1 = 7
                      E2 = 8
                      temp1 = 9
                      temp2 = 10
                      temp3 = 11
                      temp4 = 12
                      temp5 = 13
                      temp6 = 14
                      temp7 = 15
                      temp8 = 16
                      temp9 = 17
                      temp10 = 18
                      temp11 = 19
                      temp12 = 20
                      temp13 = 21
                      temp14 = 22

-- open import Data.Sum using (_⊎_; inj₁; inj₂)
-- exercise-2-1 : {A : Set} → Program Nat (A ⊎ WHILE-atom)
-- exercise-2-1 {A} = readToVar X »
--                     {!   !}
--                 »writeFromVar Y
--                 where X = 0
--                       Y = 1

-- Definition 3.2.1 --

var' : 𝔻
var' = ((nil · nil) · nil)

cons' : 𝔻
cons' = ((nil · nil) · (nil · nil))

hd' : 𝔻
hd' = (((nil · nil) · nil) · (nil · nil))

tl' : 𝔻
tl' = ((nil · (nil · nil)) · (nil · nil))

=?' : 𝔻
=?' = ((nil · nil) · ((nil · nil) · nil))

quote' : 𝔻
quote' = ((nil · nil) · nil) · (nil · (nil · nil))

expression-to-data : Expression → 𝔻
expression-to-data (var X) = var' · ((numerals X) · nil)
expression-to-data nil = quote' · nil · nil
expression-to-data (atom d) = quote' · d · nil
expression-to-data (cons E F) = cons' · (E' · (F' · nil))
                            where E' = expression-to-data E
                                  F' = expression-to-data F
expression-to-data (hd E) = (hd' · (E' · nil))
                            where E' = expression-to-data E
expression-to-data (tl E) = (tl' · (E' · nil))
                            where E' = expression-to-data E
expression-to-data (E =? F) = (=?' · (E' · (F' · nil)))
                            where E' = expression-to-data E
                                  F' = expression-to-data F

:=' : 𝔻
:=' = (nil · nil) · (nil · (nil · nil))

»' : 𝔻
»' = ((nil · nil) · (nil · nil)) · (nil · nil)

while' : 𝔻
while' = ((nil · nil) · nil) · ((nil · nil) · nil)

command-to-data : Command → 𝔻
command-to-data (var X := E) = (:=' · (varX' · (E' · nil)))
                            where varX' = expression-to-data (var X)
                                  E' = expression-to-data E
command-to-data (C » D) = (»' · (C' · (D' · nil)))
                            where C' = command-to-data C
                                  D' = command-to-data D
command-to-data (while E begin C end) = while' · (E' · (C' · nil))
                            where E' = expression-to-data E
                                  C' = command-to-data C

program-to-data : Program → 𝔻
program-to-data (read-var X » C »write-var Y)
    = varX' · (C' · (varY' · nil))
    where varX' = expression-to-data (var X)
          varY' = expression-to-data (var Y)
          C' = command-to-data C


data-to-nat : 𝔻 → Maybe Nat
data-to-nat nil = just 0
data-to-nat (nil · d) with (data-to-nat d)
...                      | just n         = just (suc n)
...                      | nothing        = nothing
data-to-nat (_ · d)   = nothing

data-to-expression : 𝔻 → Maybe Expression
data-to-expression ((((nil · nil) · nil) · (nil · (nil · nil))) · (nil · nil)) = just nil
data-to-expression ((((nil · nil) · nil) · (nil · (nil · nil))) · (d · nil)) = just (atom d)
data-to-expression (((nil · nil) · nil) · (X' · nil))
    with (data-to-nat X')
...    | just X          = just (var X)
...    | nothing         = nothing
data-to-expression (((nil · nil) · (nil · nil)) · (E' · (F' · nil)))
    with data-to-expression E' | data-to-expression F'
...    | just E                | just F                = just (cons E F)
...    | _                     | _                     = nothing
data-to-expression ((((nil · nil) · nil) · (nil · nil)) · (E' · nil))
    with data-to-expression E'
...    | just E                = just (hd E)
...    | _                     = nothing
data-to-expression (((nil · (nil · nil)) · (nil · nil)) · (E' · nil))
    with data-to-expression E'
...    | just E                = just (tl E)
...    | _                     = nothing
data-to-expression (((nil · nil) · ((nil · nil) · nil)) · (E' · (F' · nil)))
    with data-to-expression E' | data-to-expression F'
...    | just E                | just F                = just (E =? F)
...    | _                     | _                     = nothing
data-to-expression _ = nothing

data-to-command : 𝔻 → Maybe Command
data-to-command (((nil · nil) · (nil · (nil · nil))) · (varX' · (E' · nil)))
    with data-to-expression varX' | data-to-expression E'
...    | just (var X)             | just E               = just (var X := E)
...    | _                        | _                    = nothing
data-to-command ((((nil · nil) · (nil · nil)) · (nil · nil)) · (C' · (D' · nil)))
    with data-to-command C' | data-to-command D'
...    | just C             | just D            = just (C » D)
...    | _                  | _                 = nothing
data-to-command ((((nil · nil) · nil) · ((nil · nil) · nil)) · (E' · (C' · nil)))
    with data-to-expression E' | data-to-command C'
...    | just E                | just C            = just (while E begin C end)
...    | _                     | _                 = nothing
data-to-command _ = nothing

data-to-program : 𝔻 → Maybe Program
data-to-program (varX' · (C' · (varY' · nil)))
    with data-to-expression varX' | data-to-command C' | data-to-expression varY'
...    | just (var X)             | just C             | just (var Y)            = just (read-var X » C »write-var Y)
...    | _                        | _                  | _                       = nothing
data-to-program _ = nothing

data Pattern : Set where
    nil : Pattern
    var : Nat → Pattern
    _·_ : Pattern → Pattern → Pattern

data Vector (A : Set) : Nat → Set where
  []  : Vector A zero
  _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)

pattern [_,_] y z = y ∷ z ∷ []

data RewriteRule : Nat → Set where
    _⇒_ : {n : Nat} → Vector Pattern n → Vector Expression n → RewriteRule n
    _⇒_» : {n : Nat} → Vector Pattern n → Command → RewriteRule n

ruleToCommand : {n : Nat} → Vector Nat n → RewriteRule n → Command
ruleToCommand []       _                     = skip
ruleToCommand (X ∷ Xs) ((P ∷ Ps) ⇒ (E ∷ Es)) = (var X := E) » (ruleToCommand Xs (Ps ⇒ Es))
ruleToCommand _        (_ ⇒ C »)             = C

countNumbersOfNewVariableNeeded : Pattern → Nat
countNumbersOfNewVariableNeeded nil = 2
countNumbersOfNewVariableNeeded (var D) = 0
countNumbersOfNewVariableNeeded (D₁ · D₂) = 1 + (countNumbersOfNewVariableNeeded D₁) + (countNumbersOfNewVariableNeeded D₂)

patternToIfClause : Expression → Pattern → Command → {newX : Nat} → Command
patternToIfClause E nil C {newX} =
    (if E then (skip)
    else C) {newX} {suc newX}
patternToIfClause E (var D) C {newX} = C
patternToIfClause E (D₁ · D₂) C {newX} =
    (if E then (
        patternToIfClause (hd E) D₁ (
            patternToIfClause (tl E) D₂ C {newX + 1 + (countNumbersOfNewVariableNeeded D₁)}
        ) {newX + 1}
    )) {newX}

patternsToIfClause : {n : Nat} → Vector Nat n → Vector Pattern n → Command → {newX : Nat} → Command
patternsToIfClause []       []       C {_}    = C
patternsToIfClause (X ∷ Xs) (P ∷ Ps) C {newX} =
    patternToIfClause (var X) P (
        patternsToIfClause Xs Ps C {newX + (countNumbersOfNewVariableNeeded P)}
    ) {newX}

REWRITE_BY_ : {n : Nat} → Vector Nat n → List (RewriteRule n) → {newX : Nat} → Command
REWRITE_BY_ {n} _ []             {newX} = skip
REWRITE_BY_ {n} Xs (rule ∷ rules) {newX} =
    (patternsToIfClause Xs Ps (ruleToCommand Xs rule)) {newX}
    » (REWRITE Xs BY rules) {newX}
    where getPatterns : (RewriteRule n) → Vector Pattern n
          getPatterns (Ps ⇒ _)   = Ps
          getPatterns (Ps ⇒ _ ») = Ps
          Ps : Vector Pattern n
          Ps = getPatterns rule

data CaseRule : Nat → Set where
    _⇒_» : {n : Nat} → Pattern → Command → CaseRule n

CASE_OF_ : {n : Nat} → Expression → List (CaseRule n) → {newX : Nat} → Command
(CASE E OF [])                  {newX} = skip
(CASE E OF ((P ⇒ C ») ∷ rules)) {newX} =
    (patternToIfClause E P C {newX})
    » ((CASE E OF rules) {newX})

equality-test' : Program
equality-test' =
    read-var X » (
        (var GO := true)
        » (var Y := false)
        » (var D := hd (var X))
        » (var E := tl (var X))
        » while (var GO) begin (
            (REWRITE [ D , E ] BY (
                ([(((var D11) · (var D12)) · (var D2)) , (((var E11) · (var E12)) · (var E2))]
                    ⇒ [ (cons (var D11) (cons (var D12) (var D2))) , (cons (var E11) (cons (var E12) (var E2)))]
                ) ∷
                ([(((var D11) · (var D12)) · (var D2)) , (nil · (var E2))]
                    ⇒ var GO := false »
                ) ∷
                ([(((var D11) · (var D12)) · (var D2)) , nil ]
                    ⇒ var GO := false »
                ) ∷ 
                ([(nil · (var D2)) , (((var E11) · (var E12)) · (var E2))]
                    ⇒ var GO := false »
                ) ∷ 
                ([(nil · (var D2)) , (nil · (var E2))]
                    ⇒ [ var D2 , var E2 ]
                ) ∷
                ([(nil · (var D2)) , nil ]
                    ⇒ var GO := false »
                ) ∷ 
                ([ nil  , ((var E1) · (var E2))]
                    ⇒ var GO := false »
                ) ∷ 
                ([ nil , nil ]
                    ⇒ (var Y := true
                    » var GO := false) »
                ) ∷ []
            )) {n}
        ) end
    ) »write-var Y
    where X = 0
          Y = 1
          GO = 2
          D = 3
          E = 4
          D11 = 5
          D12 = 6
          D2 = 7
          E11 = 8
          E12 = 9
          E1 = 10
          E2 = 11
          n = 12
