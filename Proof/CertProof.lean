import Mathlib

-- This takes about 100 seconds;
-- I suspect the slow bit is parsing lists, which appears to be quadratic in the length of the list (hence why I've split the list into 100 parts)
import Proof.Cert
import Proof.TileDefs

import Proof.Eqns


set_option maxHeartbeats 20000000
set_option maxRecDepth 200000



def pyt_eqns : List (List (List Piece × ℚ ) × ℚ)  := allparts.map Eqns.fromAllParts


-- takes a few seconds.
-- This will be used to show that allparts form a system of linear equations
-- that hold for the volume of pieces of the Pythagoras tree
theorem allParts_describes_pyt : ∀ p ∈ allparts, p.2.1 = List.map (fun r => canon_cor_rot r p.1) [Cor.tl,Cor.br,Cor.bl,Cor.tr] := by
  native_decide

-- verifies in 5 mins. Could probably be made much faster by using hashmaps or something,
            -- I think it's spending most of its time adding 0s
-- (considering reflections would also speed it up by a factor of 4)


@[irreducible]
def pyt_sum : List (List Piece × ℚ) := (Eqns.mergeFold_acc []
   (List.mergeSort (Eqns.toCoeffs pyt_eqns) (fun x y => @decide  (toLex x ≤ toLex y) (Prod.Lex.instDecidableRelOfDecidableEq x y)  )))

/-
-- This is true, but not actually faster, hence unneccessary
theorem apeq' : pyt_sum = (init.map (fun x => (x,(1:ℚ)))).reverse ++ [([],-Eqns.qEmpty),([Piece.fullPiece],-Eqns.qFull)] := by
  native_decide -/

-- takes a few seconds.
-- This uses the coefficients in allparts to combine the equations into the one we care about
-- which gives the area of the Pythagoras tree
theorem apeq : List.Perm pyt_sum (init.map (fun x => (x,(1:ℚ))) ++ [([],-Eqns.qEmpty),([Piece.fullPiece],-Eqns.qFull) ]) := by
  native_decide


-- logically, allParts_describes_pyt tells us that Matrix.mulVec A (volume_vector) = 0
-- and apeq tells us that Matrix.vecMul qs A = r (where qs are the coefficients forming the certificate)
-- then we use
--  Matrix.mulVec A x = 0 → Matrix.vecMul v A = r →  dotProduct r x = 0
-- which says that the area of the pythagoras tree minus qFull times the area of a unit square is zero.
-- In practice, things go faster if we don't touch any matrices (working with sums of lists rather than List.toFinset is much easier)
