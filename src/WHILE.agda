
module WHILE where

open import Agda.Builtin.Nat


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

data Expressions : Set where
    var : Nat → Expressions
    nil : Expressions
    atom : 𝔻 → Expressions
    cons : Expressions → Expressions → Expressions
    hd tl : Expressions → Expressions
    _=?_ : Expressions → Expressions → Expressions


data Commands : Set where
    var_:=_ : Nat → Expressions → Commands
    _»_ : Commands → Commands → Commands
    while_begin_end : Expressions → Commands → Commands
infix 21 var_:=_
infixl 20 _»_

data Programs : Set where
    read-to-var_»_»write-from-var_ : Nat → Commands → Nat → Programs

infix 19 read-to-var_»_»write-from-var_


-- Example 2.1.4 --

reverse : Programs
reverse = read-to-var 0 » (
            var 1 := nil »
                while (var 0) begin
                    (var 1 := (cons (hd (var 0)) (var 1)) »
                    var 0 := (tl (var 0)))
                end
        ) »write-from-var 1


-- Definition 2.1.5 --

false : Expressions
false = nil

falseᴰ : 𝔻
falseᴰ = nil

true : Expressions
true = cons nil nil

trueᴰ : 𝔻
trueᴰ = nil · nil


-- Example 2.1.6. --

if_then_ : Expressions → Commands → {new : Nat} → Commands
(if E then C) {new} =
    var new := E »
    while (var new) begin
        (var new := false) »
        C
    end

if_then_else_ : Expressions → Commands → Commands → {new1 new2 : Nat} → Commands
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

not : Expressions → Expressions
not E = (E =? false)

_or_ : Expressions → Expressions → Expressions
E or F = not ((cons E F) =? true)

_and_ : Expressions → Expressions → Expressions
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

succ-one-numeral : Programs
succ-one-numeral =
    read-to-var X
        » var Y := cons nil (var X)
    »write-from-var Y
    where X = 0
          Y = 1

pred-one-numeral : Programs
pred-one-numeral =
    read-to-var X
        » var Y := tl (var X)
    »write-from-var Y
    where X = 0
          Y = 1

add-two-numerals : Programs
add-two-numerals =
    read-to-var XY
        » ((var X := hd (var XY))           -- X = first XY
        » (var Y := tl (var XY))            -- Y = second XY
        » while (var X) begin               -- while (X != 0)
            (var Y := cons nil (var Y))     --     Y = Y + 1
            » (var X := tl (var X))         --     X = X - 1
        end)
    »write-from-var Y
    where XY = 0
          X = 1
          Y = 2

skip : Commands
skip = var 0 := var 0

list : List Expressions → Expressions
list [] = nil
list (E ∷ Es) = cons E (list Es)

cons* : List Expressions → Expressions
cons* [] = nil
cons* (E ∷ []) = E
cons* (E ∷ Es) = cons E (cons* Es)

-- Example 2.1.9
-- ? How to define function call ?
-- var_:=_<<=var_ : Nat → Programs → Nat → {Nat} → Expressions

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
(σ [ X ↦ d ]) Y with X == Y
... | trueᵇ  = d
... | falseᵇ = σ Y

initial-store : (p : Programs) → 𝔻 → Store
initial-store (read-to-var X » C »write-from-var Y) d Z
    = ifᵇ (X == Z) then d else nil

σ₀ : (p : Programs) → 𝔻 → Store
σ₀ = initial-store

isEqual : 𝔻 → 𝔻 → Bool
isEqual nil     nil     = trueᵇ
isEqual nil     _       = falseᵇ
isEqual _       nil     = falseᵇ
isEqual (e · f) (g · h) = (isEqual e g) ∧ (isEqual f h)


-- Definition 2.2.2 --

E[_] : Expressions → Store → 𝔻
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


-- Definition 2.2.3 --

data _≡nil : 𝔻 → Set where
    nil≡nil : nil ≡nil

data _≢nil : 𝔻 → Set where
    cons-≢nil : (d e : 𝔻) → (d · e) ≢nil


-- Definition 2.2.3 --

data _⊢_⇒_ : (C : Commands) → (σ σ' : Store) → Set where
    assign : {E : Expressions} {X : Nat} {σ : Store}
            → (var X := E) ⊢ σ ⇒ (σ [ X ↦ (E[ E ] σ) ])
    compose : {C D : Commands} {σ σ' σ'' : Store}
            → (C ⊢ σ ⇒ σ') → (D ⊢ σ' ⇒ σ'')
            → ((C » D) ⊢ σ ⇒ σ'')
    loop-true : {E : Expressions} {C : Commands} {σ σ' σ'' : Store}
            → (E[ E ] σ) ≡nil → (C ⊢ σ ⇒ σ') → ((while E begin C end) ⊢ σ' ⇒ σ'')
            → ((while E begin C end) ⊢ σ ⇒ σ'')
    loop-false : {E : Expressions} {C : Commands} {σ : Store}
            → (E[ E ] σ) ≢nil
            → ((while E begin C end) ⊢ σ ⇒ σ)


open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ-syntax; _×_)


-- Definition 2.2.4 --

[_]_≡ : Programs → 𝔻 → 𝔻 → Set
[ read-to-var X » C »write-from-var Y ] d ≡ e
    = Σ[ σ ∈ Store ] ((C ⊢ (σ₀ p d) ⇒ σ) × ((σ Y) ≡ e))
    where p = read-to-var X » C »write-from-var Y

open import Agda.Builtin.Maybe using (Maybe; nothing; just)

_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)

[_]≡ : Programs → (𝔻 → Maybe 𝔻) → Set
[ p ]≡ f = (x y : 𝔻) → (f x ≡ just y) ↔ ([ p ] x ≡ y)

[_]_↓ : Programs → 𝔻 → Set
[ p ] d ↓ = Σ[ f ∈ (𝔻 → Maybe 𝔻) ] ([ p ]≡ f) × (
                Σ[ e ∈ 𝔻 ] (f d ≡ just e)
            )

equality-test : Programs
equality-test = read-to-var X » (
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
                ) »write-from-var Y
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
-- exercise-2-1 : {A : Set} → Programs Nat (A ⊎ WHILE-atom)
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

expression-to-data : Expressions → 𝔻
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

command-to-data : Commands → 𝔻
command-to-data (var X := E) = (:=' · (varX' · (E' · nil)))
                            where varX' = expression-to-data (var X)
                                  E' = expression-to-data E
command-to-data (C » D) = (»' · (C' · (D' · nil)))
                            where C' = command-to-data C
                                  D' = command-to-data D
command-to-data (while E begin C end) = while' · (E' · (C' · nil))
                            where E' = expression-to-data E
                                  C' = command-to-data C

program-to-data : Programs → 𝔻
program-to-data (read-to-var X » C »write-from-var Y)
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

data-to-expression : 𝔻 → Maybe Expressions
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

data-to-command : 𝔻 → Maybe Commands
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

data-to-program : 𝔻 → Maybe Programs
data-to-program (varX' · (C' · (varY' · nil)))
    with data-to-expression varX' | data-to-command C' | data-to-expression varY'
...    | just (var X)             | just C             | just (var Y)            = just (read-to-var X » C »write-from-var Y)
...    | _                        | _                  | _                       = nothing
data-to-program _ = nothing


data Pattern : Set where
    nil : Pattern
    var : Nat → Pattern
    _·_ : Pattern → Pattern → Pattern

data Vector (A : Set) : Nat → Set where
  []  : Vector A zero
  _∷_ : {n : Nat} → A → Vector A n → Vector A (suc n)

data RewriteRule : Nat → Set where
    _⇒_ : {n : Nat} → Vector Pattern n → Vector Expressions n → RewriteRule n
    _⇒_» : {n : Nat} → Vector Pattern n → Commands → RewriteRule n

ruleToCommand : {n : Nat} → Vector Nat n → RewriteRule n → Commands
ruleToCommand []       _                     = skip
ruleToCommand (X ∷ Xs) ((P ∷ Ps) ⇒ (E ∷ Es)) = (var X := E) » (ruleToCommand Xs (Ps ⇒ Es))
ruleToCommand _        (_ ⇒ C »)             = C

countNumbersOfNewVariableNeeded : Pattern → Nat
countNumbersOfNewVariableNeeded nil = 2
countNumbersOfNewVariableNeeded (var D) = 0
countNumbersOfNewVariableNeeded (D₁ · D₂) = 1 + (countNumbersOfNewVariableNeeded D₁) + (countNumbersOfNewVariableNeeded D₂)

patternToIfClause : Expressions → Pattern → Commands → {newX : Nat} → Commands
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

patternsToIfClause : {n : Nat} → Vector Nat n → Vector Pattern n → Commands → {newX : Nat} → Commands
patternsToIfClause []       []       C {_}    = C
patternsToIfClause (X ∷ Xs) (P ∷ Ps) C {newX} =
    patternToIfClause (var X) P (
        patternsToIfClause Xs Ps C {newX + (countNumbersOfNewVariableNeeded P)}
    ) {newX}

REWRITE_BY_ : {n : Nat} → Vector Nat n → List (RewriteRule n) → {newX : Nat} → Commands
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
    _⇒_» : {n : Nat} → Pattern → Commands → CaseRule n

CASE_OF_ : {n : Nat} → Expressions → List (CaseRule n) → {newX : Nat} → Commands
(CASE E OF [])                  {newX} = skip
(CASE E OF ((P ⇒ C ») ∷ rules)) {newX} =
    (patternToIfClause E P C {newX})
    » ((CASE E OF rules) {newX})

