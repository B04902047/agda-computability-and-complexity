
open import WHILE renaming
    ( Program to WHILE-program
    ; Command to WHILE-command
    )

-- Figure 4.1 --

open import Data.List using (_∷_; [])

STEP : WHILE-command
STEP = (REWRITE [ Cd , St ] BY (
            ({!   !} ⇒ [ (var Cr) , cons (var D) (var St) ])
            ∷ []
        )) {n}
    where Cd = 3
          St = 4
          D = 5
          Cr = 6
          n = 12

u1var : WHILE-program
u1var = read-var PD » (
            var P := hd (var PD)
            » var C := hd (tl (var P))
            » var Cd := cons (var C) nil
            » var St := nil
            » var Vl := tl (var PD)
            » while (var Cd) begin
                STEP
            end
        ) »write-var Vl
    where PD = 0
          P = 1
          C = 2
          Cd = 3
          St = 4
          Vl = 5