import Mathlib

import Proof.SquareDivision

open Real
open AffineMap
open Matrix
open Prod
open MeasureTheory

-- macro "R2" : term => `(ℝ × ℝ)


namespace SquareDiv

inductive Rot : Type where
  | none : Rot
  | left : Rot
  | half : Rot
  | right : Rot

def rinv (r:Rot): Rot := match r with
  | Rot.left => Rot.right
  | Rot.right => Rot.left
  | _ => r
/-
def rcor (r : Rot) (c : Cor) : Cor :=
  sorry
-/

-- Tranformation (rotate about (1/2,1/2)) sending unit_sq to unitsq
noncomputable def rotTransform (rot : Rot) : (R2 →ᵃ[ℝ] R2) := match rot with
  | Rot.none => AffineMap.id ℝ R2 --LinearMap.toAffineMap (LinearMap.id)
  | Rot.left => AffineMap.comp (AffineMap.const ℝ R2 (1/2,1/2))
                <| AffineMap.comp (LinearMap.toAffineMap (
                     Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![0, -1 ; 1, 0 ] ))
                ( AffineMap.const ℝ R2 (-1/2,-1/2))
  | Rot.half => AffineMap.comp (AffineMap.const ℝ R2 ((1/2 : ℝ) ,(1/2 : ℝ) ))
                <| AffineMap.comp
                  (LinearMap.toAffineMap ((-1 : ℝ ) • LinearMap.id))
                  (AffineMap.const ℝ R2 ((-1/2 : ℝ) ,(-1/2 : ℝ) ))
  | Rot.right => AffineMap.comp (AffineMap.const ℝ R2 (1/2,1/2))
                <| AffineMap.comp (LinearMap.toAffineMap (
                     Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![0, 1 ; -1, 0 ] ))
                (AffineMap.const ℝ R2 (-1/2,-1/2))

theorem rinv_consistent : rotTransform r (rotTransform (rinv r) x) = x := by
  sorry

theorem thm_rot {rot:Rot}: rotTransform rot '' unit_sq = unit_sq := by
  unfold rotTransform
  /-cases' rot <;> (
    simp
  )-/
  sorry
/-
theorem rcor_consistent {rot : Rot} {cor : Cor} :
  rotTransform rot '' (corTransform cor '' usq) = corTransform (rcor rot cor) '' usq := by
  sorry-/
