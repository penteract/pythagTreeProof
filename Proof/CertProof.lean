import Mathlib

-- This takes about 100 seconds;
-- I suspect the slow bit is parsing lists, which appears to be quadratic in the length of the list (hence why I've split the list into 100 parts)
import Proof.Cert
import Proof.TileDefs

import Proof.Eqns


set_option maxHeartbeats 20000000
set_option maxRecDepth 200000



def pyt_eqns : List (List (List Piece × ℚ ) × ℚ)  := allparts.map Eqns.fromAllParts
-- without defining these explicitly, Lean 4.22-rc3 tries to reevaluate them an awful lot of times
def eqfs : Finset (List (List Piece × ℚ ) × ℚ)  := (pyt_eqns).toFinset
def avfs : Finset (List Piece) := (Eqns.all_vars (pyt_eqns)).toFinset
def bigMat : Matrix eqfs
                    avfs
                    ℚ := Eqns.getMat (pyt_eqns)


-- takes a few seconds.
-- This will be used to show that allparts form a system of linear equations
-- that hold for the volume of pieces of the Pythagoras tree
theorem allParts_describes_pyt : ∀ p ∈ allparts, p.2.1 = List.map (fun r => canon_cor_rot r p.1) [Cor.tl,Cor.br,Cor.bl,Cor.tr] := by
  native_decide

-- verifies in 5 mins. Could probably be made much faster by using hashmaps or something,
            -- I think it's spending most of its time adding 0s
-- (considering reflections would also speed it up by a factor of 4)
-- This uses the coefficients in allparts to combine the equations into the one we care about
-- which gives the area of the Pythagoras tree

--#eval! (Eqns.mergeFold (List.mergeSort (Eqns.toCoeffs pyt_eqns)))
theorem allParts_makes_eqn :
    Matrix.vecMul (fun e => e.val.snd) bigMat =
    (fun v => if v.val=[] then -Eqns.qEmpty else
              if v.val=[Piece.fullPiece] then -Eqns.qFull else
              if v.val ∈ init then 1 else 0 ) := by
  unfold bigMat pyt_eqns Eqns.fromAllParts
  -- sorry
  with_unfolding_all native_decide


def eqn_parts := ([]::[Piece.fullPiece]::init).toFinset


theorem eqn_parts_ss_allvars : eqn_parts ⊆ (Eqns.all_vars pyt_eqns).toFinset := by
  native_decide
