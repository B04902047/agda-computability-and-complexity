
module Language where

open import Data.Maybe using (Maybe; just; nothing; map)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import WHILE using (_↔_)

IsFunctional : {A B : Set} (R : A → B → Set) → Set
IsFunctional {A} {B} R = (x : A) → Σ[ y ∈ B ] ((R x y) × ((y' : B) → R x y' → y ≡ y'))

-- Definition 3.1.1 --

record Language (Programs : Set) (Data : Set) : Set₁ where
    field
        [_]_≃_ : Programs → Data → Data → Set
        -- int-isFunctional : IsFunctional [_]≡
    
    [_]≡ : Programs → (Data → Maybe Data) → Set
    [ p ]≡ f = (x y : Data) → ([ p ] x ≃ y) ↔ (f x ≡ just y)

    [_]≡' : Programs → (Data → Data → Set) → Set
    [ p ]≡' R = (x y : Data) → ([ p ] x ≃ y) ↔ (R x y)
    
    has-program-as-data : Set
    has-program-as-data = Programs → Data

    has-pairing : Set
    has-pairing = Data → Data → Data

IsSubset : Set → Set → Set₁
IsSubset A Data = Σ[ P ∈ (Data → Set) ] (A ↔ (Σ[ x ∈ Data ] (P x)))
-- × (Data -> Maybe A)

open import WHILE using () renaming (
      𝔻 to WHILE-data
    ; Program to WHILE-program
    ; program-to-data to WHILE-program-to-data
    ; [_]_≡ to [_]ᵂᴴᴵᴸᴱ_≡
    )

WHILE : Language WHILE-program WHILE-data
WHILE = record {
        [_]_≃_ = [_]ᵂᴴᴵᴸᴱ_≡
    }

WHILE-has-program-as-data : Language.has-program-as-data WHILE
WHILE-has-program-as-data = WHILE-program-to-data


-- Definition 3.1.2 --

_can-simulate_ : {M-program L-program Data : Set}
                → Language M-program Data
                → Language L-program Data
                → Set
_can-simulate_ {M-program} {L-program} {Data} M L
    = (p : L-program)
    → Σ[ q ∈ M-program ] (
        (f : Data → Maybe Data)
        → ([ p ]ᴸ≡ f ↔ [ q ]ᴹ≡ f)
    )
    where [_]ᴸ≡ = Language.[_]≡ L
          [_]ᴹ≡ = Language.[_]≡ M


_is-equivalent-to_ : {M-program L-program Data : Set}
                → Language M-program Data → Language L-program Data
                → Set
M is-equivalent-to L = (M can-simulate L) × (L can-simulate M)


-- Definition 3.3.1 --

IsCompilingFunction : {ST-data S-program T-program L-data : Set}
                        → IsSubset S-program L-data
                        → IsSubset T-program L-data
                        → (f : L-data → L-data)
                        → (S : Language S-program ST-data)
                        → (T : Language T-program ST-data)
                        → Set
IsCompilingFunction {ST-data} {S-program} {T-program} {L-data} (Is-S-program , S→L , L→S) (Is-T-program , T→L , L→T) f S T
    = (p : L-data) → (p∈S : Is-S-program p)
    → Σ[ fp∈T ∈ (Is-T-program (f p)) ] (
        (d e : ST-data)
        → ([ (L→S (p , p∈S)) ]ˢ d ≃ e) ↔ ([ (L→T (f p , fp∈T)) ]ᵀ d ≃ e)
    )
    where [_]ˢ_≃_ = Language.[_]_≃_ S
          [_]ᵀ_≃_ = Language.[_]_≃_ T


IsHighLevelCompilingFunction : {Data S-program T-program : Set}
                    → (g : S-program → T-program)
                    → (S : Language S-program Data)
                    → (T : Language T-program Data)
                    → Set
IsHighLevelCompilingFunction {Data} {S-program} {T-program} g S T
    = {p : S-program}
    → {d e : Data}
    → ([ p ]ˢ d ≃ e)
    ↔ ([ (g p) ]ᵀ d ≃ e)
    where [_]ˢ_≃_ = Language.[_]_≃_ S
          [_]ᵀ_≃_ = Language.[_]_≃_ T

_realizes_ : {S-program T-program L-data : Set}
            → (f : L-data → L-data)
            → (g : S-program → T-program)
            → IsSubset S-program L-data
            → IsSubset T-program L-data
            → Set
_realizes_ {S-program} {T-program} {L-data} f g (Is-S-program , S→L , L→S) (Is-T-program , T→L , L→T)
    = ( (p : L-data)
        → (p∈S : Is-S-program p)
        → Σ[ fp∈T ∈ Is-T-program (f p) ] (
            (g (L→S (p , p∈S))) ≡ L→T ((f p), fp∈T)
        )
    )


IsCompilingFunction' : {ST-data S-program T-program L-data : Set}
                    → IsSubset S-program L-data
                    → IsSubset T-program L-data
                    → (f : L-data → L-data)
                    → (S : Language S-program ST-data)
                    → (T : Language T-program ST-data)
                    → Set
IsCompilingFunction' {ST-data} {S-program} {T-program} {L-data} S⊆L T⊆L f S T
    = Σ[ g ∈ (S-program → T-program) ] (
        (IsHighLevelCompilingFunction g S T)
        × ((f realizes g) S⊆L T⊆L)
    )

open import Relation.Binary.PropositionalEquality using (sym; subst)

alt-def : {ST-data S-program T-program L-data : Set}
    → {S⊆L : IsSubset S-program L-data}
    → {T⊆L : IsSubset T-program L-data}
    → {f : L-data → L-data}
    → {S : Language S-program ST-data}
    → {T : Language T-program ST-data}
    → IsCompilingFunction' {ST-data} {S-program} {T-program} {L-data} S⊆L T⊆L f S T
    → IsCompilingFunction {ST-data} {S-program} {T-program} {L-data} S⊆L T⊆L f S T
alt-def {ST-data} {S-program} {T-program} {L-data}
    {S⊆L@(Is-S-program , S→L , L→S)} {T⊆L@(Is-T-program , T→L , L→T)} {f} {S} {T}
    (g , g-isHighLevelCompilingFunction , f-realizes-g ) p p∈S
    = (fp∈T , λ d e → (only-if-direction d e , if-direction d e)  )
    where fp∈T : Is-T-program (f p)
          fp∈T = proj₁ (f-realizes-g p p∈S)
          [_]ˢ_≃_ = Language.[_]_≃_ S
          [_]ᵀ_≃_ = Language.[_]_≃_ T
          only-if-direction : (d e : ST-data)
                → ([ (L→S (p , p∈S)) ]ˢ d ≃ e)
                → ([ (L→T (f p , fp∈T)) ]ᵀ d ≃ e) -- (g (L→S (p , p∈S))) ≡ L→T ((f p), fp∈T)
          only-if-direction d e [p]d≃e = [fp]d≃e
                where gp≡fp : (g (L→S (p , p∈S))) ≡ L→T ((f p), fp∈T)
                      gp≡fp = proj₂ (f-realizes-g p p∈S)
                      [gp]d≃e : [ g (L→S (p , p∈S)) ]ᵀ d ≃ e
                      [gp]d≃e = (proj₁ g-isHighLevelCompilingFunction) [p]d≃e
                      [fp]d≃e : [ L→T (f p , fp∈T) ]ᵀ d ≃ e
                      [fp]d≃e = subst (λ p → [ p ]ᵀ d ≃ e) gp≡fp [gp]d≃e
          if-direction : (d e : ST-data)
                → ([ (L→T (f p , fp∈T)) ]ᵀ d ≃ e)
                → ([ (L→S (p , p∈S)) ]ˢ d ≃ e)
          if-direction d e [fp]d≃e = [p]d≃e
                where gp≡fp : (g (L→S (p , p∈S))) ≡ L→T ((f p), fp∈T)
                      gp≡fp = proj₂ (f-realizes-g p p∈S)
                      fp≡gp : L→T ((f p), fp∈T) ≡ (g (L→S (p , p∈S)))
                      fp≡gp = sym gp≡fp
                      [gp]d≃e : [ g (L→S (p , p∈S)) ]ᵀ d ≃ e
                      [gp]d≃e = subst (λ p → [ p ]ᵀ d ≃ e) fp≡gp [fp]d≃e
                      [p]d≃e : [ (L→S (p , p∈S)) ]ˢ d ≃ e
                      [p]d≃e = (proj₂ g-isHighLevelCompilingFunction) [gp]d≃e


IsTotal : {A : Set} → (A → Maybe A) → Set
IsTotal {A} f = (x : A) → Σ[ y ∈ A ] (f x ≡ just y)

toTotal : {A : Set} → (f : A → Maybe A) → IsTotal f → (A → A)
toTotal f f-isTotal x = proj₁ (f-isTotal x)

IsCompiler : {ST-data S-program T-program L-data L-program : Set}
            → IsSubset S-program L-data
            → IsSubset T-program L-data
            → (comp : L-program)
            → (S : Language S-program ST-data)
            → (T : Language T-program ST-data)
            → (L : Language L-program L-data)
            → Set
IsCompiler {ST-data} {S-program} {T-program} {L-data} {L-program} S⊆L T⊆L comp S T L
    = Σ[ f ∈ (L-data → Maybe L-data) ] (
        [ comp ]ᴸ≡ f
        × Σ[ f-isTotal ∈ (IsTotal f) ] (
            IsCompilingFunction S⊆L T⊆L (toTotal f f-isTotal) S T
        )
    )
    where [_]ᴸ≡ = Language.[_]≡ L

-- simulates-implies-a-compiling-function : {ST-data S-program T-program L-data : Set}
--                                 → {S⊆L : IsSubset S-program L-data}
--                                 → {T⊆L : IsSubset T-program L-data}
--                                 → {S : Language S-program ST-data}
--                                 → {T : Language T-program ST-data}
--                                 → T can-simulate S
--                                 → Σ[ f ∈ (L-data → L-data) ] (
--                                     IsCompilingFunction' {ST-data} {S-program} {T-program} {L-data} S⊆L T⊆L f S T
--                                 )
-- simulates-implies-a-compiling-function {ST-data} {S-program} {T-program} {L-data}
--     {S⊆L@(Is-S-program , S→L , L→S)} {T⊆L@(Is-T-program , T→L , L→T)}
--     {S} {T}
--     T-can-simulate-S
--     = (f , g , g-isHighLevelCompilingFunction , f-realizes-g)
--     where [_]ˢ_≃_ = Language.[_]_≃_ S
--           [_]ᵀ_≃_ = Language.[_]_≃_ T
--           g : S-program → T-program
--           g p = proj₁ (T-can-simulate-S p)
--           g-isHighLevelCompilingFunction : {p : S-program}
--                                             → {d e : ST-data}
--                                             → ([ p ]ˢ d ≃ e)
--                                             ↔ ([ (g p) ]ᵀ d ≃ e)
--           g-isHighLevelCompilingFunction {p} {d} {e} = ({!   !} , {!   !})
--           f : L-data → L-data
--           f = {!   !}
--           f-realizes-g : (p : L-data)
--                         → (p∈S : Is-S-program p)
--                         → Σ[ fp∈T ∈ Is-T-program (f p) ] (
--                             (g (L→S (p , p∈S))) ≡ L→T ((f p), fp∈T)
--                         )
--           f-realizes-g = {!   !}

compiling-function-simulates : {ST-data S-program T-program L-data : Set}
                                → {S⊆L : IsSubset S-program L-data}
                                → {T⊆L : IsSubset T-program L-data}
                                → {f : L-data → L-data}
                                → {S : Language S-program ST-data}
                                → {T : Language T-program ST-data}
                                → IsCompilingFunction' {ST-data} {S-program} {T-program} {L-data} S⊆L T⊆L f S T
                                → T can-simulate S
compiling-function-simulates {ST-data} {S-program} {T-program} {L-data}
    {S⊆L@(Is-S-program , S→L , L→S)} {T⊆L@(Is-T-program , T→L , L→T)}
    {f} {S} {T}
    f-is-compiling-function@(
        g ,
        g-isHighLevelCompilingFunction ,
        f-realizes-g
    ) p = (g p , [p]ˢ≡[gp]ᵀ)
    where [_]ˢ≡ = Language.[_]≡ S
          [_]ᵀ≡ = Language.[_]≡ T
          [_]ˢ_≃_ = Language.[_]_≃_ S
          [_]ᵀ_≃_ = Language.[_]_≃_ T
          [p]ˢ≡[gp]ᵀ : (f : ST-data → Maybe ST-data)
                    → ([ p ]ˢ≡ f ↔ [ g p ]ᵀ≡ f)
          [p]ˢ≡[gp]ᵀ f = (only-if-direction , if-direction)
                where only-if-direction : ((x y : ST-data) → ([ p ]ˢ x ≃ y) ↔ (f x ≡ just y))
                                        → ((x y : ST-data) → ([ g p ]ᵀ x ≃ y) ↔ (f x ≡ just y))
                      only-if-direction [p]ˢ≡f x y = ( only-if-direction' , if-direction')
                            where [p]ˢx≃y←[gp]ᵀx≃y : [ g p ]ᵀ x ≃ y → [ p ]ˢ x ≃ y
                                  [p]ˢx≃y←[gp]ᵀx≃y = proj₂ (g-isHighLevelCompilingFunction {p} {x} {y})
                                  only-if-direction' : ([ g p ]ᵀ x ≃ y) → (f x ≡ just y)
                                  only-if-direction' [gp]ᵀx≃y = (proj₁ ([p]ˢ≡f x y)) ([p]ˢx≃y←[gp]ᵀx≃y [gp]ᵀx≃y)
                                  [p]ˢx≃y→[gp]ᵀx≃y : [ p ]ˢ x ≃ y → [ g p ]ᵀ x ≃ y
                                  [p]ˢx≃y→[gp]ᵀx≃y = proj₁ (g-isHighLevelCompilingFunction {p} {x} {y})
                                  if-direction' : f x ≡ just y → [ g p ]ᵀ x ≃ y
                                  if-direction' fx≡y = [p]ˢx≃y→[gp]ᵀx≃y ((proj₂ ([p]ˢ≡f x y)) fx≡y)
                      if-direction : ((x y : ST-data) → ([ g p ]ᵀ x ≃ y) ↔ (f x ≡ just y))
                                    → ((x y : ST-data) → ([ p ]ˢ x ≃ y) ↔ (f x ≡ just y))
                      if-direction [gp]ᵀ≡f x y = (only-if-direction' , if-direction')
                            where [p]ˢx≃y→[gp]ᵀx≃y : [ p ]ˢ x ≃ y → [ g p ]ᵀ x ≃ y
                                  [p]ˢx≃y→[gp]ᵀx≃y = proj₁ (g-isHighLevelCompilingFunction {p} {x} {y})
                                  only-if-direction' : ([ p ]ˢ x ≃ y) → (f x ≡ just y)
                                  only-if-direction' [p]ˢx≃y = (proj₁ ([gp]ᵀ≡f x y)) ([p]ˢx≃y→[gp]ᵀx≃y [p]ˢx≃y)
                                  [p]ˢx≃y←[gp]ᵀx≃y : [ g p ]ᵀ x ≃ y → [ p ]ˢ x ≃ y
                                  [p]ˢx≃y←[gp]ᵀx≃y = proj₂ (g-isHighLevelCompilingFunction {p} {x} {y})
                                  if-direction' : (f x ≡ just y) → ([ p ]ˢ x ≃ y)
                                  if-direction' fx≡y = [p]ˢx≃y←[gp]ᵀx≃y ((proj₂ ([gp]ᵀ≡f x y)) fx≡y)

-- -- Definition 3.3.2 --

Is-one-to-one : {A B : Set} (f : A → B) → Set
Is-one-to-one {A} {B} f = (x y : A) → (f x ≡ f y) → x ≡ y

Coding : (A B : Set) → Set
Coding A B = Σ[ f ∈ (A → B)] (Is-one-to-one f)

_implements_by_ : {A B : Set} (g : B → Maybe B) → (f : A → Maybe A) → (c : Coding A B) → Set
_implements_by_ {A} {B} g f (c , c-is-injection) = (a : A) → (g (c a)) ≡ (map c) (f a)


-- -- Definition 3.3.3 --

-- IsRelativeCompilingFunction : {S-data T-data L-data : Set}
--                         {Is-S-program Is-T-program : L-data → Set}
--                         → (f : (p : L-data) → L-data)
--                         → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) S-data)
--                         → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) T-data)
--                         → (c : Coding S-data T-data)
--                         → Set
-- IsRelativeCompilingFunction {S-data} {T-data} {L-data} {Is-S-program} {Is-T-program} f S T c
--     = {p : L-data}
--     → (p' : Is-S-program p)
--     → Σ[ fp' ∈ (Is-T-program (f p)) ] (
--         (g : S-data → Maybe S-data)
--         → [(p , p')]ˢ≡ g
--         → (h : T-data → Maybe T-data)
--         → [(f p , fp')]ᵀ≡ h
--         → h implements g by c
--     )
--     where [_]ˢ≡ = Language.[_]≡ S
--           [_]ᵀ≡ = Language.[_]≡ T

-- IsRelativeCompiler : {S-data T-data L-data L-program : Set}
--             {Is-S-program Is-T-program : L-data → Set}
--             → (comp : L-program)
--             → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) S-data)
--             → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) T-data)
--             → (L : Language L-program L-data)
--             → (c : Coding S-data T-data)
--             → Set
-- IsRelativeCompiler {S-data} {T-data} {L-data} {L-program} {Is-S-program} {Is-T-program} comp S T L c
--     = Σ[ f ∈ (L-data → Maybe L-data) ] (
--         [ comp ]ᴸ≡ f
--         × Σ[ f-isTotal ∈ (IsTotal f) ] (
--             IsRelativeCompilingFunction (toTotal f f-isTotal) S T c
--         )
--     )
--     where [_]ᴸ≡ = Language.[_]≡ L


-- -- Definition 3.4.1 --

                        

IsInterpretingFunction : {Data S-program : Set}
            → (i : Data → Maybe Data)
            → (S : Language S-program Data)
            → (_” : Language.has-program-as-data S)
            → (_·ˢ_ : Language.has-pairing S)
            → Set
IsInterpretingFunction {Data} {S-program} i S _” _·ˢ_
    = (p : S-program)
    → (d : Data)
    → (e : Data)
    → (i ((p ”) ·ˢ d) ≡ just e)
    → [ p ]ˢ d ≃ e
    where [_]ˢ_≃_ = Language.[_]_≃_ S

IsInterpreter : {Data L-program S-program : Set}
            → (int : L-program)
            → (L : Language L-program Data)
            → (S : Language S-program Data)
            → (_” : Language.has-program-as-data S)
            → (_·ˢ_ : Language.has-pairing S)
            → Set
IsInterpreter {Data} {L-program} {S-program} int L S _” _·ˢ_
    = Σ[ i ∈ (Data → Maybe Data) ] (
        IsInterpretingFunction {Data} {S-program} i S _” _·ˢ_
    )

-- -- Definition 3.6.1 --

-- IsSpecializingFunction : {Data : Set}
--             {Is-S-program Is-T-program : Data → Set}
--             → (f  : Data → Data)
--             → (S : Language (Σ[ p ∈ Data ] (Is-S-program p)) Data)
--             → (T : Language (Σ[ p ∈ Data ] (Is-T-program p)) Data)
--             → (_·_ : Language.has-pairing S)
--             → Set
-- IsSpecializingFunction {Data} {Is-S-program} {Is-T-program} f S T _·_
--     = {p : Data}
--     → (p∈S : Is-S-program p)
--     → (s d : Data)
--     → Σ[ fps∈T ∈ (Is-T-program (f (p · s)))] (
--         {[p]ˢ [fps]ᵀ : Data → Maybe Data}
--         → [ p , p∈S ]ˢ≡ [p]ˢ
--         → [ f (p · s) , fps∈T ]ᵀ≡ [fps]ᵀ
--         → [p]ˢ (s · d) ≡ [fps]ᵀ d
--     )
--     where [_]ˢ≡ = Language.[_]≡ S
--           [_]ᵀ≡ = Language.[_]≡ T

-- IsSpecializer : {Data L-program : Set}
--             {Is-S-program Is-T-program : Data → Set}
--             → (spec  : L-program)
--             → (S : Language (Σ[ p ∈ Data ] (Is-S-program p)) Data)
--             → (T : Language (Σ[ p ∈ Data ] (Is-T-program p)) Data)
--             → (L : Language L-program Data)
--             → (_·_ : Language.has-pairing S)
--             → Set
-- IsSpecializer {Data} {L-program} {Is-S-program} {Is-T-program} spec S T L _·_
--     = Σ[ f ∈ (Data → Maybe Data)] (
--         [ spec ]ᴸ≡ f
--         × Σ[ f-isTotal ∈ (IsTotal f) ] (
--             IsSpecializingFunction (toTotal f f-isTotal) S T _·_
--         )
--     )
--     where [_]ᴸ≡ = Language.[_]≡ L 