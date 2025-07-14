import Mathlib

-- This takes about 100 seconds;
-- I suspect the slow bit is parsing lists, which appears to be quadratic in the length of the list (hence why I've split the list into 100 parts)
import Proof.Cert

import Proof.Eqns

def init : List (List Piece) :=
  (List.finRange 7).flatMap
    (fun i => (List.finRange 4).map
      (fun j => [Piece.treePiece i j 0]))

set_option maxHeartbeats 20000000
set_option maxRecDepth 200000



def pyt_eqns : List (List (List Piece × ℚ ) × ℚ)  := allparts.map (fun (a,b,q) => ((a,4)::b.map (·,-1) ,q) )
-- def pyt_eqns' : List (List (List Piece × ℚ ) × ℚ)  := allparts.map Eqns.fromAllParts
/-
def bigMat' : Matrix (allparts.map Eqns.fromAllParts).toFinset
                    (Eqns.all_vars (allparts.map Eqns.fromAllParts)).toFinset
                    ℚ := Eqns.getMat (allparts.map Eqns.fromAllParts)
-/
def bigMat : Matrix (pyt_eqns).toFinset
                    (Eqns.all_vars (pyt_eqns)).toFinset
                    ℚ := Eqns.getMat (pyt_eqns)


-- takes a few seconds.
-- This will be used to show that allparts form a system of linear equations
-- that hold for the volume of pieces of the Pythagoras tree
theorem allParts_describes_pyt : ∀ p ∈ allparts, p.2.1 = List.map (fun r => canon_cor_rot r p.1) [Cor.tl,Cor.br,Cor.bl,Cor.tr] := by
  native_decide


/-
-- def hdap := List.head allparts (by simp [allparts,part1])
def hdap := allparts[1]!

#eval hdap.2.1 = List.map (fun r => canon_cor_rot r hdap.1)  [Cor.tl,Cor.br,Cor.bl,Cor.tr]

#eval hdap.2.1
#eval List.map (fun r => canon_cor_rot r hdap.1) [Cor.tl,Cor.br,Cor.bl,Cor.tr]
-/

-- verifies in 5 mins. Could probably be made much faster by using hashmaps or something,
            -- I think it's spending most of its time adding 0s
-- (considering reflections would also speed it up by a factor of 4)
-- This uses the coefficients in allparts to combine the equations into the one we care about
-- which gives the area of the Pythagoras tree

theorem allParts_makes_eqn :
    Matrix.vecMul (fun e => e.val.snd) bigMat =
    (fun v => if v.val=[] then -qEmpty else
              if v.val=[Piece.fullPiece] then -qFull else
              if v.val ∈ init then 1 else 0 ) := by
  with_unfolding_all native_decide
