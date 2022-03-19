

open import WHILE renaming (
      Programs to WHILE-programs
    ; [_]≡ to [_]ᵂᴴᴵᴸᴱ≡
    ; [_]_≡ to [_]ᵂᴴᴵᴸᴱ_≡
    ; [_]_↓ to [_]ᵂᴴᴵᴸᴱ_↓
    ; program-to-data to _ᴰ
    )

open import Data.Maybe using (Maybe)
open import Data.Product using (Σ-syntax; _×_; _,_)

-- Definition 5.1.1 --

Is-WHILE-computable : (f : 𝔻 → Maybe 𝔻) → Set
Is-WHILE-computable f = Σ[ p ∈ WHILE-programs ] ([ p ]ᵂᴴᴵᴸᴱ≡ f)

Is-WHILE-decidable : (A : 𝔻 → Set) → Set
Is-WHILE-decidable A = Σ[ p ∈ WHILE-programs ] (
                        (d : 𝔻) → (
                            ([ p ]ᵂᴴᴵᴸᴱ d ↓)
                          × ((A d) ↔ [ p ]ᵂᴴᴵᴸᴱ d ≡ trueᴰ)
                        )
                    )

Is-WHILE-semi-decidable : (A : 𝔻 → Set) → Set
Is-WHILE-semi-decidable A = Σ[ p ∈ WHILE-programs ] (
                            (d : 𝔻) → ((A d) ↔ [ p ]ᵂᴴᴵᴸᴱ d ≡ trueᴰ)
                        )

data ∅ {A : Set} : A → Set where

data Is-WHILE-enumerable : (A : 𝔻 → Set) → Set where
    ∅-is-enumerable : Is-WHILE-enumerable ∅
    case2 : {A : 𝔻 → Set} → (p : WHILE-programs) → (
                ((d : 𝔻) → (Σ[ e ∈ 𝔻 ] ([ p ]ᵂᴴᴵᴸᴱ d ≡ e) × A e))
              × ((e : 𝔻) → A e → Σ[ d ∈ 𝔻 ] ([ p ]ᵂᴴᴵᴸᴱ d ≡ e))
            ) → Is-WHILE-enumerable A

-- Theorem 5.2.1 --

open import Data.List using (_∷_; [])

spec : WHILE-programs
spec = read-to-var PS » (
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
        ) »write-from-var NewP
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

spec-is-specializer : (p : WHILE-programs)
                        → (s : 𝔻)
                        → Σ[ pₛ ∈ WHILE-programs ] (
                            ( [ spec ]ᵂᴴᴵᴸᴱ ((p ᴰ) · s) ≡ (pₛ ᴰ))
                            × ( (d : 𝔻)
                                → (e : 𝔻)
                                → ( ([ pₛ ]ᵂᴴᴵᴸᴱ d ≡ e)
                                    ↔ ([ p ]ᵂᴴᴵᴸᴱ (s · d) ≡ e)
                                )
                            )
                        )
spec-is-specializer (read-to-var X » C »write-from-var Y) s
    = ((read-to-var X » C »write-from-var Y),
        (
            (
                ? ,
                ?
            ) ,
            ?
        )
    )
    where pₛ = read-to-var X » (
                var X := cons (atom s) (var X)
                » C
               ) »write-from-var Y

Kleene's-SMN-theorem : Σ[ spec ∈ WHILE-programs ] (
                            (p : WHILE-programs)
                            → (s : 𝔻)
                            → Σ[ pₛ ∈ WHILE-programs ] (
                                ( [ spec ]ᵂᴴᴵᴸᴱ ((p ᴰ) · s) ≡ (pₛ ᴰ))
                                × ( (d : 𝔻)
                                    → (e : 𝔻)
                                    → ( ([ pₛ ]ᵂᴴᴵᴸᴱ d ≡ e)
                                        ↔ ([ p ]ᵂᴴᴵᴸᴱ (s · d) ≡ e)
                                    )
                                )
                            )
                        )
Kleene's-SMN-theorem = (spec , spec-is-specializer)
 