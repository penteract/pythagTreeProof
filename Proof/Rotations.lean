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
-- (Fin 2 → ℝ)


-- open Module

lemma fnrnk : FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  rw [finrank_euclideanSpace, Fintype.card_fin]
/-
instance : Fact (FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) where
  out := by rw [finrank_euclideanSpace, Fintype.card_fin]

instance : Fact (FiniteDimensional.finrank ℝ ((Fin (↑(1+1))) → ℝ) = 2) where
  out := by

    rewrite [← (@fnrnk 2)]
    rewrite [(@fnrnk 2)]
    nth_rewrite 0 [(@fnrnk 2)]
    nth_rewrite 1 [← (@fnrnk 2).out]
    apply LinearEquiv.finrank_eq
    symm
    exact (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv
-/
instance : Fact (FiniteDimensional.finrank ℝ (ℝ × ℝ) = 2) where
  out := by
    rw [← @fnrnk 2]
    apply LinearEquiv.finrank_eq
    symm
    exact LinearEquiv.trans (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv (LinearEquiv.finTwoArrow ℝ ℝ )


/-
#check (Orientation.rightAngleRotation _ : R2 ≃ₗᵢ[ℝ] R2)
#check (Orientation.rightAngleRotation _ : (Fin 2 → ℝ) ≃ₗᵢ[ℝ] (Fin 2 → ℝ))

theorem d2 : FiniteDimensional.finrank ℝ R2 = 2 := by
  sorry
theorem d2' : FiniteDimensional.finrank ℝ (Fin 2 → ℝ) = 2 := by
  sorry

#check Orientation.rightAngleRotation

#check (Orientation.rightAngleRotation : (o : Orientation ℝ R2 (Fin 2)) →  R2 ≃ₗᵢ[ℝ] R2)
#check (Orientation.rightAngleRotation _ : R2 ≃ₗᵢ[ℝ] R2)

#check @Orientation.rightAngleRotation (Fin 2 → ℝ) _ _

def rotLeft (o : Orientation ℝ R2 (Fin 2)) : R2 ≃ₗᵢ[ℝ] R2 := by
  exact (Orientation.rightAngleRotation o)

def rotLeft'' (o :  @Orientation ℝ strictOrderedCommSemiring (ℝ × ℝ) AddCommGroup.toAddCommMonoid
    (@NormedSpace.toModule ℝ (ℝ × ℝ) normedField NormedAddCommGroup.toSeminormedAddCommGroup
      InnerProductSpace.toNormedSpace)
    (Fin 2))
   : _ -- R2 ≃ₗᵢ[ℝ] R2 :=
  := (Orientation.rightAngleRotation o)

def rotLeft' (o : Orientation ℝ (Fin 2 → ℝ) (Fin 2)) : (Fin 2 → ℝ) ≃ᵃⁱ[ℝ] (Fin 2 → ℝ) := by
  have h := Fact.mk d2'

  exact (Orientation.rightAngleRotation o)
-/

noncomputable def rotLeft : R2 ≃ₗ[ℝ] R2 := by
  let ml : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1 ; 1, 0 ]
  let mr : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 ; -1, 0 ]
  have hmlmr : ml*mr = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
  have hmrml : mr*ml = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
  exact Matrix.toLinOfInv (Basis.finTwoProd _) (Basis.finTwoProd _) hmlmr hmrml
  -- exact (Matrix.toLinearEquiv (Basis.finTwoProd _) m h)


noncomputable def rotLeft' : R2 ≃ₗ[ℝ] R2 := by
  let m : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1 ; 1, 0 ]
  have h : IsUnit m.det := by
    simp [Matrix.det_fin_two,m]
  exact (Matrix.toLinearEquiv (Basis.finTwoProd _) m h)


noncomputable def rotRight' : R2 ≃ₗ[ℝ] R2 := by
  let m : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 ; -1, 0 ]
  have h : IsUnit m.det := by
    simp [Matrix.det_fin_two,m]
  exact (Matrix.toLinearEquiv (Basis.finTwoProd _) m h)


/-
theorem rsymm : rotRight = rotLeft.symm := by
  ext ⟨x,y⟩
  unfold rotLeft rotRight
  simp
  -/
@[simp]
noncomputable def conj (a b : R2 ≃ᵃ[ℝ] R2) := AffineEquiv.trans (AffineEquiv.trans b.symm a) b

-- Tranformation (rotate about (1/2,1/2)) sending unit_sq to unitsq
noncomputable def rotTransform (rot : Rot) : (R2 ≃ᵃ[ℝ] R2) := match rot with
  | Rot.none => AffineEquiv.refl ℝ R2 --LinearMap.toAffineMap (LinearMap.id)
  | Rot.left => conj rotLeft.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv
  | Rot.half => AffineEquiv.homothetyUnitsMulHom ⟨1/2,1/2⟩ (-1)
  | Rot.right => conj rotLeft.symm.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv



theorem rinv_consistent : rotTransform r (rotTransform (rinv r) x) = x := by
  obtain ⟨x,y⟩ := x
  cases' r <;>(
    unfold rotTransform rinv
    simp
    )
  . unfold rotLeft
    simp [AffineIsometryEquiv.constVAdd, AffineIsometryEquiv.symm]
  . unfold homothety
    simp
  unfold rotLeft
  simp [AffineIsometryEquiv.constVAdd,AffineIsometryEquiv.symm]


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
