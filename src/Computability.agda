

open import WHILE renaming (
      Program to WHILE-program
    ; program-to-data to _ᴰ
    ; data-to-program to _ᵂᴴᴵᴸᴱ
    )

open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

-- Definition 5.1.1 --

Is-WHILE-computable : (f : 𝔻 → 𝔻 → Set) → Set
Is-WHILE-computable f = Σ[ p ∈ WHILE-program ] ([ p ]≡ f)

Is-WHILE-decidable : (A : 𝔻 → Set) → Set
Is-WHILE-decidable A = Σ[ p ∈ WHILE-program ] (
                        (d : 𝔻) → (
                            ([ p ] d ↓) × (
                                (A d) ↔ [ p ] d ≡ trueᴰ
                            )
                        )
                    )

Is-WHILE-semi-decidable : (A : 𝔻 → Set) → Set
Is-WHILE-semi-decidable A = Σ[ p ∈ WHILE-program ] (
                            (d : 𝔻) → ((A d) ↔ [ p ] d ≡ trueᴰ)
                        )

Is-WHILE-enumerable : (A : 𝔻 → Set) → Set
Is-WHILE-enumerable A = Σ[ p ∈ WHILE-program ] (
                            (a : 𝔻) → (A a) ↔ (
                                Σ[ (d , b) ∈ (𝔻 × 𝔻) ] (
                                    Σ[ b' ∈ 𝔻 ] (
                                        [ p ] d ≡ (b · a)
                                    )
                                )
                            )
                        )

Is-nontrivially-WHILE-enumerable : (A : 𝔻 → Set) → Set
Is-nontrivially-WHILE-enumerable A =
    Σ[ p ∈ WHILE-program ] (
        ((d : 𝔻) → (Σ[ e ∈ 𝔻 ] ([ p ] d ≡ e) × A e))
        × ((e : 𝔻) → A e → Σ[ d ∈ 𝔻 ] ([ p ] d ≡ e))
    )

-- -- Theorem 5.2.1 --

open import Data.List using (_∷_; [])

spec : WHILE-program
spec = read-var PS » (
            var P := hd (var PS)
            » var S := tl (var S)
            » var Vari := hd (var P)
            » var C := hd (tl (var P))
            » var Varj := hd (tl (tl (var P)))
            » var QuoteS := list ((atom quote') ∷ (var S) ∷ [])
            » var ConsExp := list ((atom cons') ∷ (var QuoteS) ∷ (var Vari) ∷ [])
            » var AssignX := list ((atom =?') ∷ (var Vari) ∷ (var ConsExp) ∷ [])
            » var NewC := list ((atom »') ∷ (var AssignX) ∷ (var C) ∷ [])
            » var NewP := list ((var Vari) ∷ (var NewC) ∷ (var Varj) ∷ [])
        ) »write-var NewP
    where PS = 0
          P = 1
          S = 2
          Vari = 3
          C = 4
          Varj = 5
          QuoteS = 6
          ConsExp = 7
          AssignX = 8
          NewC = 9
          NewP = 10

-- spec-is-specializer : (p : WHILE-program)
--                         → (s : 𝔻)
--                         → Σ[ pₛ ∈ WHILE-program ] (
--                             ( [ spec ] ((p ᴰ) · s) ≡ (pₛ ᴰ))
--                             × ( (d : 𝔻)
--                                 → (e : 𝔻)
--                                 → ( ([ pₛ ] d ≡ e)
--                                     ↔ ([ p ] (s · d) ≡ e)
--                                 )
--                             )
--                         )
-- spec-is-specializer (read-var X » C »write-var Y) s
--     = ((read-var X » C »write-var Y),
--         (
--             (
--                 {!   !} ,
--                 {!   !}
--             ) ,
--             {!   !}
--         )
--     )
--     where pₛ = read-var X » (
--                 var X := cons (atom s) (var X)
--                 » C
--                ) »write-var Y

-- Kleene's-SMN-theorem : Σ[ spec ∈ WHILE-program ] (
--                             (p : WHILE-program)
--                             → (s : 𝔻)
--                             → Σ[ pₛ ∈ WHILE-program ] (
--                                 ( [ spec ] ((p ᴰ) · s) ≡ (pₛ ᴰ))
--                                 × ( (d : 𝔻)
--                                     → (e : 𝔻)
--                                     → ( ([ pₛ ] d ≡ e)
--                                         ↔ ([ p ] (s · d) ≡ e)
--                                     )
--                                 )
--                             )
--                         )
-- Kleene's-SMN-theorem = (spec , spec-is-specializer)

open import Relation.Nullary using (¬_)
open import Data.Maybe using (nothing)
open import Data.Product using (proj₁)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _==_; suc)

-- The Halting Problem --

data halt_≡_ : 𝔻 → 𝔻 → Set₁ where
    t : {p : WHILE-program} {d : 𝔻} → [ p ] d ↓ → halt ((p ᴰ) · d) ≡ trueᴰ
    f1 : halt nil ≡ falseᴰ
    f2 : {d₁ d₂ : 𝔻} → ((d₁ ᵂᴴᴵᴸᴱ) ≡ nothing) → halt (d₁ · d₂) ≡ falseᴰ
    f3 : {p : WHILE-program} {d : 𝔻} → ¬ ([ p ] d ↓) → halt ((p ᴰ) · d) ≡ falseᴰ

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; subst; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)

open import Data.Bool using (Bool; _∧_) renaming
    ( if_then_else_ to ifᵇ_then_else_
    ; true to trueᵇ
    ; false to falseᵇ
    )


postulate
    procedure-call-store : {E : Expression} {A new : Nat} {σ : Store}
                 {p : WHILE-program} {d : 𝔻}
                → [ p ] (E[ E ] σ) ≡ d
                → (var A := p ⟨ E ⟩) {new} ⊢ σ ⇒ (σ [ A ↦ d ])
    procedure-call-store' : {E : Expression} {A new : Nat} {σ σ' : Store}
                            {p : WHILE-program} {d : 𝔻}
                            → [ p ] (E[ E ] σ) ≡ d
                            → (var A := p ⟨ E ⟩) {new} ⊢ σ ⇒ σ'
                            → E[ var A ] σ' ≡ d

loop-forever : {Y : Nat} {σ σ' : Store}
            → ¬ ((E[ var Y ] σ) ≡ nil)
            → (while (var Y) begin (var Y := var Y) end) ⊢ σ ⇒ σ'
            → ⊥
loop-forever {Y} {σ} {σ'} E[Y]σ≢nil (loop-false E[Y]σ≡nil) = E[Y]σ≢nil E[Y]σ≡nil
loop-forever {Y} {σ} {σ''} E[Y]σ≢nil (loop-true {var Y} {var Y := var Y} {σ} {σ'} {σ''}
                                                E[Y]σ≢nil'
                                                skip⊢σ⇒σ'@(assign {var Y} {Y} {σ})
                                                while⊢σ'⇒σ''
                                     )
    = loop-forever {Y} {σ'} {σ''} E[Y]σ'≢nil while⊢σ'⇒σ''
    where E[Y]σ'≢nil : ¬ ((E[ var Y ] σ') ≡ nil)
          E[Y]σ'≢nil E[Y]σ'≡nil = E[Y]σ≢nil E[Y]σ≡nil
            where E[Y]σ≡nil : (E[ var Y ] σ) ≡ nil
                  E[Y]σ≡nil = begin
                                E[ var Y ] σ
                            ≡⟨⟩ 
                                σ Y
                            ≡⟨ claim ⟩
                                (ifᵇ (Y == Y) then (σ Y) else (σ Y))
                            ≡⟨⟩ 
                                (σ [ Y ↦ σ Y ]) Y
                            ≡⟨⟩ 
                                (σ [ Y ↦ E[ var Y ] σ ]) Y
                            ≡⟨⟩
                                σ' Y
                            ≡⟨⟩ 
                                E[ var Y ] σ'
                            ≡⟨ E[Y]σ'≡nil ⟩ 
                                nil
                            ∎
                    where claim : σ Y ≡ (ifᵇ Y == Y then σ Y else σ Y)
                          claim with Y == Y
                          ...      | trueᵇ = refl
                          ...      | falseᵇ = refl

-- skip-store : (σ : Store) → skip ⊢ σ ⇒ σ


if-false-then-store : {E : Expression} {C : Command} {σ : Store}
                    → {new : Nat}
                    → (E[ E ] σ) ≡ nil
                    → ((if E then C) {new}) ⊢ σ ⇒ (σ [ new ↦ nil ])
if-false-then-store {E} {C} {σ} {new} E[E]σ≡nil = compose C₀⊢σ⇒σ' C₁⊢σ'⇒σ'
  where C₀ = var new := E
        C₁ = while (var new) begin
                C
                » (var new := false)
            end
        σ' = σ [ new ↦ nil ]
        C₀⊢σ⇒σ' : C₀ ⊢ σ ⇒ σ'
        C₀⊢σ⇒σ' = subst (λ d → C₀ ⊢ σ ⇒ (σ [ new ↦ d ])) E[E]σ≡nil assign
        E[new]σ'≡nil : (E[ (var new) ] σ') ≡ nil
        E[new]σ'≡nil = subst-proof σ new nil
        C₁⊢σ'⇒σ' : C₁ ⊢ σ' ⇒ σ'
        C₁⊢σ'⇒σ' = loop-false E[new]σ'≡nil

if-true-then-store : {E : Expression} {C : Command} {σ σ' : Store} {new : Nat}
                    → C ⊢ (σ [ new ↦ (E[ E ] σ) ]) ⇒ σ'
                    → ¬ (E[ E ] σ) ≡ nil
                    → ((if E then C) {new}) ⊢ σ ⇒ (σ' [ new ↦ nil ])
if-true-then-store {E} {C} {σ} {σ'} {new} C⊢σ⇒σ' E[E]σ≢nil = compose C₀⊢σ⇒σ₁ C₁⊢σ₁⇒σ₁₀₂
  where C₀ = var new := E
        σ₁ = σ [ new ↦ (E[ E ] σ) ]
        C₁ = while (var new) begin        
                C
                » (var new := false)
            end
        C₁₀ = C » (var new := false)
        C₁₀₀ = C
        σ₁₀₁ = σ'
        C₁₀₁ = (var new := false)
        σ₁₀₂ = σ' [ new ↦ nil ]
        C₀⊢σ⇒σ₁ : C₀ ⊢ σ ⇒ σ₁
        C₀⊢σ⇒σ₁ = subst (λ d → C₀ ⊢ σ ⇒ (σ [ new ↦ d ])) refl assign
        C₁₀₀⊢σ₁⇒σ₁₀₁ : C₁₀₀ ⊢ σ₁ ⇒ σ₁₀₁
        C₁₀₀⊢σ₁⇒σ₁₀₁ = C⊢σ⇒σ'
        C₁₀₁⊢σ₁₀₁⇒σ₁₀₂ : C₁₀₁ ⊢ σ₁₀₁ ⇒ σ₁₀₂
        C₁₀₁⊢σ₁₀₁⇒σ₁₀₂ = assign
        C₁₀⊢σ₁⇒σ₁₀₂ : C₁₀ ⊢ σ₁ ⇒ σ₁₀₂
        C₁₀⊢σ₁⇒σ₁₀₂ = compose C₁₀₀⊢σ₁⇒σ₁₀₁ C₁₀₁⊢σ₁₀₁⇒σ₁₀₂
        C₁⊢σ₁₀₂⇒σ₁₀₂ : C₁ ⊢ (σ' [ new ↦ nil ]) ⇒ (σ' [ new ↦ nil ])
        C₁⊢σ₁₀₂⇒σ₁₀₂ = loop-false {var new} {C₁₀} {σ' [ new ↦ nil ]} (subst-proof σ' new nil)
        C₁⊢σ₁⇒σ₁₀₂ : C₁ ⊢ σ₁ ⇒ σ₁₀₂
        C₁⊢σ₁⇒σ₁₀₂ = loop-true {var new} {C₁₀} {σ₁} {σ₁₀₂} {σ₁₀₂} E[new]σ₁≢nil C₁₀⊢σ₁⇒σ₁₀₂ C₁⊢σ₁₀₂⇒σ₁₀₂
            where claim : (ifᵇ (new == new) then (E[ E ] σ) else (σ new)) ≡ (E[ E ] σ)
                  claim = if-X≡X-then-d-else-e new (E[ E ] σ) (σ new)
                  E[new]σ₁≢nil : ¬ (ifᵇ (new == new) then (E[ E ] σ) else (σ new)) ≡ nil
                  E[new]σ₁≢nil = subst (λ d → ¬ d ≡ nil) (sym claim) E[E]σ≢nil


if-true-then-store' : {E : Expression} {C : Command} {σ σ'''' : Store} {new : Nat}
                    → ¬ ((E[ E ] σ) ≡ nil)
                    → ((if E then C) {new}) ⊢ σ ⇒ σ''''
                    → Σ[ (σ' , σ'') ∈ (Store × Store) ] (C ⊢ σ' ⇒ σ'')
if-true-then-store' {E} {C} {σ} {σ''''} {new} E[E]σ≢nil
    if⊢σ⇒σ'''' @(
        compose {new:=E} {while} {σ} {σ'} {σ''''}
                new:=E⊢σ⇒σ' @(assign {E} {new} {σ})
                while⊢σ'⇒σ''''
    ) with while⊢σ'⇒σ''''
...      | loop-true {var new} {while-body} {σ'} {σ'''} {σ''''} E[new]σ'≢nil
                    while-body⊢σ'⇒σ''' @(
                        compose {C} {new:=false} {σ'} {σ''} {σ'''}
                                C⊢σ'⇒σ''
                                new:=false⊢σ''⇒σ'''
                    )
                    while⊢σ'''⇒σ'''' = ((σ' , σ'') , C⊢σ'⇒σ'')
...      | loop-false {var new} {while-body} {σ'} E[new]σ'≡nil = ⊥-elim (E[new]σ'≢nil E[new]σ'≡nil)
                where E[new]σ'≡E[E]σ : E[ var new ] σ' ≡ E[ E ] σ
                      E[new]σ'≡E[E]σ = if-X≡X-then-d-else-e new (E[ E ] σ) (σ new)
                      E[new]σ'≢nil : ¬ ((E[ var new ] σ') ≡ nil)
                      E[new]σ'≢nil = subst (λ d → ¬ (d ≡ nil)) (sym E[new]σ'≡E[E]σ) E[E]σ≢nil


if-true-then-store'' : {Y : Nat} {C : Command} {σ σ'''' : Store} {new : Nat}
                    → ¬ ((E[ (var Y) ] σ) ≡ nil)
                    → ((if (var Y) then C) {new}) ⊢ σ ⇒ σ''''
                    → Σ[ (σ' , σ'') ∈ (Store × Store) ] ((C ⊢ σ' ⇒ σ'') × (¬ ((E[ (var Y) ] σ') ≡ nil)))
if-true-then-store'' {Y} {C} {σ} {σ''''} {new} E[Y]σ≢nil
    if⊢σ⇒σ'''' @(
        compose {new:=Y} {while} {σ} {σ'} {σ''''}
                new:=Y⊢σ⇒σ' @(assign {var Y} {new} {σ})
                while⊢σ'⇒σ''''
    ) with while⊢σ'⇒σ''''
...      | loop-true {var new} {while-body} {σ'} {σ'''} {σ''''} E[new]σ'≢nil
                    while-body⊢σ'⇒σ''' @(
                        compose {C} {new:=false} {σ'} {σ''} {σ'''}
                                C⊢σ'⇒σ''
                                new:=false⊢σ''⇒σ'''
                    )
                    while⊢σ'''⇒σ'''' = ((σ' , σ'') , C⊢σ'⇒σ'' , E[Y]σ'≢nil)
                       where E[Y]σ'≡E[Y]σ : E[ var Y ] σ' ≡ E[ var Y ] σ
                             E[Y]σ'≡E[Y]σ = begin
                                                E[ var Y ] σ'
                                            ≡⟨⟩
                                                σ' Y
                                            ≡⟨⟩
                                                (σ [ new ↦ (E[ var Y ] σ) ]) Y
                                            ≡⟨⟩
                                                (ifᵇ (new == Y) then (σ Y) else E[ var Y ] σ)
                                            ≡⟨⟩
                                                (ifᵇ (new == Y) then (σ Y) else (σ Y))
                                            ≡⟨ claim (σ Y) (new == Y) ⟩
                                                σ Y
                                            ≡⟨⟩
                                                E[ var Y ] σ
                                            ∎
                                    where claim : {A : Set} (x : A) (b : Bool) → (ifᵇ b then x else x) ≡ x
                                          claim _ trueᵇ = refl
                                          claim _ falseᵇ = refl
                             E[Y]σ'≢nil : ¬ (E[ var Y ] σ' ≡ nil)
                             E[Y]σ'≢nil = subst (λ d → ¬ (d ≡ nil)) (sym E[Y]σ'≡E[Y]σ) (E[Y]σ≢nil)
                             -- E[Y]σ'≢nil E[Y]σ'≡nil = E[Y]σ≢nil (subst (_≡ nil) E[Y]σ'≡E[Y]σ E[Y]σ'≡nil)
...      | loop-false {var new} {while-body} {σ'} E[new]σ'≡nil = ⊥-elim (E[new]σ'≢nil E[new]σ'≡nil)
                where E[new]σ'≡E[E]σ : E[ var new ] σ' ≡ E[ var Y ] σ
                      E[new]σ'≡E[E]σ = if-X≡X-then-d-else-e new (E[ var Y ] σ) (σ new)
                      E[new]σ'≢nil : ¬ ((E[ var new ] σ') ≡ nil)
                      E[new]σ'≢nil = subst (λ d → ¬ (d ≡ nil)) (sym E[new]σ'≡E[E]σ) E[Y]σ≢nil

-- Theorem 5.3.1 --

theorem-5-3-1 : (q : WHILE-program) → ¬ ([ q ]≡ (halt_≡_))
theorem-5-3-1 q [q]≡halt = case2 case1
      where X = 0
            Y = 1
            XX = 2
            temp = 3
            max = 4
            C₀ = (var Y := q ⟨ (cons (var X) (var X)) ⟩) {max}
            C₁ = (if (var Y) then (
                    while (var Y) begin (var Y := var Y) end
                )) {temp}
            C = C₀ » C₁
            r : WHILE-program
            r = read-var X » C »write-var Y
            σ₀ʳ = initial-store r (r ᴰ)
            E[X]≡r : E[ var X ] σ₀ʳ ≡ (r ᴰ)
            E[X]≡r = initial-store-proof' r (r ᴰ)
            E[consXX]≡rr : E[ (cons (var X) (var X)) ] σ₀ʳ ≡ ((r ᴰ) · (r ᴰ))
            E[consXX]≡rr = begin
                                E[ (cons (var X) (var X)) ] σ₀ʳ
                            ≡⟨⟩
                                (E[ (var X) ] σ₀ʳ) · (E[ (var X) ] σ₀ʳ)
                            ≡⟨ cong (_· (E[ (var X) ] σ₀ʳ)) E[X]≡r ⟩
                                (r ᴰ) · (E[ (var X) ] σ₀ʳ)
                            ≡⟨ cong ((r ᴰ) ·_) E[X]≡r ⟩
                                (r ᴰ) · (r ᴰ)
                            ∎
            case1 : ([ r ] (r ᴰ) ↓) → ⊥
            case1 [r]r↓ = (claim2 (claim1 [r]r↓)) [r]r↓
                  where claim1 : ([ r ] (r ᴰ) ↓) → [ q ] ((r ᴰ) · (r ᴰ)) ≡ trueᴰ
                        claim1 [r]r↓@(y , [r]r=y) = [q]⟨r·r⟩≡true
                              where halt⟨r·r⟩≡true : halt ((r ᴰ) · (r ᴰ)) ≡ trueᴰ
                                    halt⟨r·r⟩≡true = t {r} {r ᴰ} [r]r↓
                                    [q]⟨r·r⟩≡true : [ q ] ((r ᴰ) · (r ᴰ)) ≡ trueᴰ
                                    [q]⟨r·r⟩≡true = (proj₁ ([q]≡halt ((r ᴰ) · (r ᴰ)) trueᴰ)) halt⟨r·r⟩≡true
                        claim2 : [ q ] ((r ᴰ) · (r ᴰ)) ≡ trueᴰ → ¬ ([ r ] (r ᴰ) ↓)
                        claim2 [q]⟨r·r⟩≡true [r]r↓ @(
                                    y , [r]r≡y @ (
                                        σ₅ , C⊢σ₀ʳσ₅ @(
                                            compose {C₀} {C₁} {σ₀ʳ} {σ₁} {σ₅}
                                                    (C₀⊢σ₀ʳ⇒σ₁)
                                                    (C₁⊢σ₁⇒σ₅)
                                        ) , σ₅r≡y
                                    )
                                ) = loop-forever {Y} {σ₂} {σ₃} E[Y]σ₂≢nil forever-loop-stops
                              where [q]consXX≡false : [ q ] (E[ (cons (var X) (var X)) ] σ₀ʳ) ≡ trueᴰ
                                    [q]consXX≡false = subst (λ d → [ q ] d ≡ trueᴰ) (sym E[consXX]≡rr) [q]⟨r·r⟩≡true
                                    E[Y]σ'≡true : (E[ var Y ] σ₁) ≡ (nil · nil)
                                    E[Y]σ'≡true = procedure-call-store' {cons (var X) (var X)} {Y} {max} {σ₀ʳ} {σ₁} {q} {trueᴰ} [q]consXX≡false C₀⊢σ₀ʳ⇒σ₁
                                    E[Y]σ₁≢nil : ¬ ((E[ var Y ] σ₁) ≡ nil)
                                    E[Y]σ₁≢nil σ₁Y≡nil = true≢false (trans (sym E[Y]σ'≡true) σ₁Y≡nil)
                                        where true≢false : ¬ ((nil · nil) ≡ nil)
                                              true≢false ()
                                    loop = while (var Y) begin (var Y := var Y) end
                                    ⟨⟨σ₂,σ₃⟩,⟨loop⊢σ₂⇒σ₃,E[Y]σ'≢nil⟩⟩ : Σ[ (σ₂ , σ₃) ∈ (Store × Store) ] (loop ⊢ σ₂ ⇒ σ₃) × ¬ (E[ var Y ] σ₂ ≡ nil)
                                    ⟨⟨σ₂,σ₃⟩,⟨loop⊢σ₂⇒σ₃,E[Y]σ'≢nil⟩⟩ = if-true-then-store'' {Y} {loop} {σ₁} {σ₅} {temp} E[Y]σ₁≢nil C₁⊢σ₁⇒σ₅
                                    σ₂ = proj₁ (proj₁ ⟨⟨σ₂,σ₃⟩,⟨loop⊢σ₂⇒σ₃,E[Y]σ'≢nil⟩⟩)
                                    σ₃ = proj₂ (proj₁ ⟨⟨σ₂,σ₃⟩,⟨loop⊢σ₂⇒σ₃,E[Y]σ'≢nil⟩⟩)
                                    forever-loop-stops : loop ⊢ σ₂ ⇒ σ₃
                                    forever-loop-stops = proj₁ (proj₂ ⟨⟨σ₂,σ₃⟩,⟨loop⊢σ₂⇒σ₃,E[Y]σ'≢nil⟩⟩)
                                    E[Y]σ₂≢nil : ¬ ((E[ var Y ] σ₂) ≡ nil)
                                    E[Y]σ₂≢nil = proj₂ (proj₂ ⟨⟨σ₂,σ₃⟩,⟨loop⊢σ₂⇒σ₃,E[Y]σ'≢nil⟩⟩)
            case2 : (([ r ] (r ᴰ) ↓) → ⊥) → ⊥
            case2 ¬[r]r↓ = ¬[r]r↓ (claim2 (claim1 ¬[r]r↓))
                  where claim1 : ¬ ([ r ] (r ᴰ) ↓) → [ q ] ((r ᴰ) · (r ᴰ)) ≡ falseᴰ
                        claim1 ¬[r]r↓ = [q]⟨r·r⟩≡false
                              where halt⟨r·r⟩≡false : halt ((r ᴰ) · (r ᴰ)) ≡ falseᴰ
                                    halt⟨r·r⟩≡false = f3 {r} {r ᴰ} ¬[r]r↓
                                    [q]⟨r·r⟩≡false : [ q ] ((r ᴰ) · (r ᴰ)) ≡ falseᴰ
                                    [q]⟨r·r⟩≡false = (proj₁ ([q]≡halt ((r ᴰ) · (r ᴰ)) falseᴰ)) halt⟨r·r⟩≡false
                        claim2 : [ q ] ((r ᴰ) · (r ᴰ)) ≡ falseᴰ → ([ r ] (r ᴰ) ↓)
                        claim2 [q]⟨r·r⟩≡false = [r]r↓
                              where [r]r↓ : [ r ] (r ᴰ) ↓
                                    [r]r↓ = (falseᴰ , [r]r≡false)
                                      where [r]r≡false : Σ[ σ ∈ Store ] ((C ⊢ σ₀ʳ ⇒ σ) × ((σ Y) ≡ falseᴰ))
                                            [r]r≡false = (σ'' , C⊢σ₀ʳ⇒σ'' , refl)
                                                  where σ' = σ₀ʳ [ Y ↦ falseᴰ ]
                                                        σ'' = σ' [ temp ↦ nil ]
                                                        C⊢σ₀ʳ⇒σ'' : C ⊢ σ₀ʳ ⇒ σ''
                                                        C⊢σ₀ʳ⇒σ'' = compose C₀⊢σ₀ʳ⇒σ' C₁⊢σ'⇒σ''
                                                          where C₀⊢σ₀ʳ⇒σ' : C₀ ⊢ σ₀ʳ ⇒ σ'
                                                                C₀⊢σ₀ʳ⇒σ' = procedure-call-store [q]consXX≡false
                                                                  where [q]consXX≡false : [ q ] (E[ (cons (var X) (var X)) ] σ₀ʳ) ≡ falseᴰ
                                                                        [q]consXX≡false = subst (λ d → [ q ] d ≡ falseᴰ) rr≡E[consXX] [q]⟨r·r⟩≡false
                                                                          where rr≡E[consXX] : ((r ᴰ) · (r ᴰ)) ≡ E[ (cons (var X) (var X)) ] σ₀ʳ
                                                                                rr≡E[consXX] = sym E[consXX]≡rr
                                                                C₁⊢σ'⇒σ'' : C₁ ⊢ σ' ⇒ σ''
                                                                C₁⊢σ'⇒σ'' = if-false-then-store E[temp]σ'≡nil
                                                                  where E[temp]σ'≡nil : (E[ var temp ] σ') ≡ nil
                                                                        E[temp]σ'≡nil = subst-proof σ' temp nil

