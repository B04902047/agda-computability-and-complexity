
module Language where

open import Data.Maybe using (Maybe; just; nothing; map)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)

IsFunctional : {A B : Set} (R : A → B → Set) → Set
IsFunctional {A} {B} R = (x : A) → Σ[ y ∈ B ] ((R x y) × ((y' : B) → R x y' → y ≡ y'))

-- Definition 3.1.1 --

record Language (Programs : Set) (Data : Set) : Set₁ where
    field
        [_]≡ : Programs → (Data → Maybe Data) → Set
        -- int-isFunctional : IsFunctional [_]≡
    
    [_]_≃ : Programs → Data → Maybe Data → Set
    [ p ] x ≃ y = Σ[ f ∈ (Data → Maybe Data) ] (f x ≡ y)
    
    has-program-as-data : Set
    has-program-as-data = Programs → Data

    has-pairing : Set
    has-pairing = Data → Data → Data


open import WHILE
    using (
      [_]ᵂᴴᴵᴸᴱ≡
    ) renaming (
      𝔻 to WHILE-data
    ; Programs to WHILE-programs
    ; program-to-data to WHILE-program-to-data
    )

WHILE : Language WHILE-programs WHILE-data
WHILE = record {
        [_]≡ = [_]ᵂᴴᴵᴸᴱ≡
    }

WHILE-has-program-as-data : Language.has-program-as-data WHILE
WHILE-has-program-as-data = WHILE-program-to-data


_↔_ : Set → Set → Set
A ↔ B = (A → B) × (B → A)


-- Definition 3.1.2 --

_can-simulate_ : {M-programs L-programs Data : Set}
                → Language M-programs Data → Language L-programs Data
                → Set
_can-simulate_ {M-programs} {L-programs} {Data} M L
    = (p : L-programs)
    → Σ[ q ∈ M-programs ] (
        (f : Data → Maybe Data)
        → ([ p ]ᴸ≡ f ↔ [ q ]ᴹ≡ f)
    )
    where [_]ᴸ≡ = Language.[_]≡ L
          [_]ᴹ≡ = Language.[_]≡ M


_is-equivalent-to_ : {M-programs L-programs Data : Set}
                → Language M-programs Data → Language L-programs Data
                → Set
M is-equivalent-to L = (M can-simulate L) × (L can-simulate M)


-- Definition 3.3.1 --

IsCompilingFunction : {ST-data L-data : Set}
                        {Is-S-program Is-T-program : L-data → Set}
                        → (f : (p : L-data) → L-data)
                        → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) ST-data)
                        → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) ST-data)
                        → Set
IsCompilingFunction {ST-data} {L-data} {Is-S-program} {Is-T-program} f S T
    = {p : L-data}
    → (p' : Is-S-program p)
    → Σ[ fp' ∈ Is-T-program (f p) ] (
        (g : ST-data → Maybe ST-data)
        → ([(p , p')]ˢ≡ g ↔ [(f p , fp')]ᵀ≡ g)
    )
    where [_]ˢ≡ = Language.[_]≡ S
          [_]ᵀ≡ = Language.[_]≡ T

IsTotal : {A : Set} → (A → Maybe A) → Set
IsTotal {A} f = (x : A) → Σ[ y ∈ A ] (f x ≡ just y)

toTotal : {A : Set} → (f : A → Maybe A) → IsTotal f → (A → A)
toTotal f f-isTotal x = proj₁ (f-isTotal x)

IsCompiler : {ST-data L-data L-programs : Set}
            {Is-S-program Is-T-program : L-data → Set}
            → (comp : L-programs)
            → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) ST-data)
            → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) ST-data)
            → (L : Language L-programs L-data)
            → Set
IsCompiler {ST-data} {L-data} {L-programs} {Is-S-program} {Is-T-program} comp S T L
    = Σ[ f ∈ (L-data → Maybe L-data) ] (
        [ comp ]ᴸ≡ f
        × Σ[ f-isTotal ∈ (IsTotal f) ] (
            IsCompilingFunction (toTotal f f-isTotal) S T
        )
    )
    where [_]ᴸ≡ = Language.[_]≡ L

can-simulate-with-compiling-function : {ST-data L-data : Set}
                                        {Is-S-program Is-T-program : L-data → Set}
                                        → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) ST-data)
                                        → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) ST-data)
                                        → (f : L-data → L-data)
                                        → (IsCompilingFunction f S T)
                                        → T can-simulate S
can-simulate-with-compiling-function {ST-data} {L-data} {Is-S-program} {Is-T-program} S T f f-is-compiling-function (p , p')
    = ((f p , proj₁ (f-is-compiling-function p')) , proj₂ (f-is-compiling-function p'))


-- Definition 3.3.2 --

Is-one-to-one : {A B : Set} (f : A → B) → Set
Is-one-to-one {A} {B} f = (x y : A) → (f x ≡ f y) → x ≡ y

Coding : (A B : Set) → Set
Coding A B = Σ[ f ∈ (A → B)] (Is-one-to-one f)

_implements_by_ : {A B : Set} (g : B → Maybe B) → (f : A → Maybe A) → (c : Coding A B) → Set
_implements_by_ {A} {B} g f (c , c-is-injection) = (a : A) → (g (c a)) ≡ (map c) (f a)


-- Definition 3.3.3 --

IsRelativeCompilingFunction : {S-data T-data L-data : Set}
                        {Is-S-program Is-T-program : L-data → Set}
                        → (f : (p : L-data) → L-data)
                        → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) S-data)
                        → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) T-data)
                        → (c : Coding S-data T-data)
                        → Set
IsRelativeCompilingFunction {S-data} {T-data} {L-data} {Is-S-program} {Is-T-program} f S T c
    = {p : L-data}
    → (p' : Is-S-program p)
    → Σ[ fp' ∈ (Is-T-program (f p)) ] (
        (g : S-data → Maybe S-data)
        → [(p , p')]ˢ≡ g
        → (h : T-data → Maybe T-data)
        → [(f p , fp')]ᵀ≡ h
        → h implements g by c
    )
    where [_]ˢ≡ = Language.[_]≡ S
          [_]ᵀ≡ = Language.[_]≡ T

IsRelativeCompiler : {S-data T-data L-data L-programs : Set}
            {Is-S-program Is-T-program : L-data → Set}
            → (comp : L-programs)
            → (S : Language (Σ[ p ∈ L-data ] (Is-S-program p)) S-data)
            → (T : Language (Σ[ p ∈ L-data ] (Is-T-program p)) T-data)
            → (L : Language L-programs L-data)
            → (c : Coding S-data T-data)
            → Set
IsRelativeCompiler {S-data} {T-data} {L-data} {L-programs} {Is-S-program} {Is-T-program} comp S T L c
    = Σ[ f ∈ (L-data → Maybe L-data) ] (
        [ comp ]ᴸ≡ f
        × Σ[ f-isTotal ∈ (IsTotal f) ] (
            IsRelativeCompilingFunction (toTotal f f-isTotal) S T c
        )
    )
    where [_]ᴸ≡ = Language.[_]≡ L


-- Definition 3.4.1 --


IsInterpretingFunction : {Data L-programs : Set}
            {Is-S-program : Data → Set}
            → (i : Data → Maybe Data)
            → (S : Language (Σ[ p ∈ Data ] (Is-S-program p)) Data)
            → (L : Language L-programs Data)
            → (_·_ : Language.has-pairing S)
            → Set
IsInterpretingFunction {Data} {L-programs} {Is-S-program} i S L _·_
    = (p : Data)
    → (p∈S : Is-S-program p)
    → (d : Data)
    → [ p , p∈S ]ˢ d ≃ (i (p · d))
    where [_]ˢ_≃ = Language.[_]_≃ S

IsIntepreter : {Data L-programs : Set}
            {Is-S-program : Data → Set}
            → (int : L-programs)
            → (S : Language (Σ[ p ∈ Data ] (Is-S-program p)) Data)
            → (L : Language L-programs Data)
            → (_·_ : Language.has-pairing S)
            → Set
IsIntepreter {Data} {L-programs} {Is-S-program} int S L _·_
    = Σ[ i ∈ (Data → Maybe Data)] (
        [ int ]ᴸ≡ i
        × (IsInterpretingFunction i S L _·_)
    )
    where [_]ᴸ≡ = Language.[_]≡ L
                        

IsInterpretingFunction' : {Data L-programs S-programs : Set}
            → (i : Data → Maybe Data)
            → (L : Language L-programs Data)
            → (S : Language S-programs Data)
            → (_” : Language.has-program-as-data S)
            → (_·ˢ_ : Language.has-pairing S)
            → Set
IsInterpretingFunction' {Data} {L-programs} {S-programs} i L S _” _·ˢ_
    = (p : S-programs)
    → (d : Data)
    → [ p ]ˢ d ≃ (i ((p ”) ·ˢ d))
    where [_]ˢ_≃ = Language.[_]_≃ S



-- Definition 3.6.1 --

IsSpecializingFunction : {Data : Set}
            {Is-S-program Is-T-program : Data → Set}
            → (f  : Data → Data)
            → (S : Language (Σ[ p ∈ Data ] (Is-S-program p)) Data)
            → (T : Language (Σ[ p ∈ Data ] (Is-T-program p)) Data)
            → (_·_ : Language.has-pairing S)
            → Set
IsSpecializingFunction {Data} {Is-S-program} {Is-T-program} f S T _·_
    = {p : Data}
    → (p∈S : Is-S-program p)
    → (s d : Data)
    → Σ[ fps∈T ∈ (Is-T-program (f (p · s)))] (
        {[p]ˢ [fps]ᵀ : Data → Maybe Data}
        → [ p , p∈S ]ˢ≡ [p]ˢ
        → [ f (p · s) , fps∈T ]ᵀ≡ [fps]ᵀ
        → [p]ˢ (s · d) ≡ [fps]ᵀ d
    )
    where [_]ˢ≡ = Language.[_]≡ S
          [_]ᵀ≡ = Language.[_]≡ T

IsSpecializer : {Data L-programs : Set}
            {Is-S-program Is-T-program : Data → Set}
            → (spec  : L-programs)
            → (S : Language (Σ[ p ∈ Data ] (Is-S-program p)) Data)
            → (T : Language (Σ[ p ∈ Data ] (Is-T-program p)) Data)
            → (L : Language L-programs Data)
            → (_·_ : Language.has-pairing S)
            → Set
IsSpecializer {Data} {L-programs} {Is-S-program} {Is-T-program} spec S T L _·_
    = Σ[ f ∈ (Data → Maybe Data)] (
        [ spec ]ᴸ≡ f
        × Σ[ f-isTotal ∈ (IsTotal f) ] (
            IsSpecializingFunction (toTotal f f-isTotal) S T _·_
        )
    )
    where [_]ᴸ≡ = Language.[_]≡ L