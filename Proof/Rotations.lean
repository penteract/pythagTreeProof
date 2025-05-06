import Mathlib

import Proof.SquareDivision

open Real
open AffineMap
open Matrix
open Prod
open MeasureTheory

-- macro "R2" : term => `(ℝ × ℝ)


-- namespace SquareDiv
open SquareDiv


noncomputable def rotLeft : R2 ≃ₗ[ℝ] R2 := by
  let ml : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1 ; 1, 0 ]
  let mr : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 ; -1, 0 ]
  have hmlmr : ml*mr = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
  have hmrml : mr*ml = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
  exact Matrix.toLinOfInv (Basis.finTwoProd _) (Basis.finTwoProd _) hmlmr hmrml
  -- exact (Matrix.toLinearEquiv (Basis.finTwoProd _) m h)

inductive Rot : Type where
  | none : Rot
  | left : Rot
  | half : Rot
  | right : Rot

def rinv (r:Rot): Rot := match r with
  | Rot.left => Rot.right
  | Rot.right => Rot.left
  | _ => r

@[simp]
noncomputable def conj (a b : R2 ≃ᵃ[ℝ] R2) := AffineEquiv.trans (AffineEquiv.trans b.symm a) b
@[simp]
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


theorem thm_rot {rot:Rot}: rotTransform rot '' usq = usq := by
  have h (b:ℝ ) (z:ℝ) : 2⁻¹ + (2⁻¹ + -b) = z ↔ b = 1-z := by
    norm_num
    bound
  have h' (b:ℝ ) (z:ℝ) : 2⁻¹ - b + 2⁻¹ = z ↔ b = 1-z := by
    norm_num
    bound
  ext ⟨x,y⟩
  cases' rot
  unfold usq square
  simp
  . unfold usq square
    simp [rotLeft,AffineIsometryEquiv.constVAdd]
    simp [← and_assoc,h]
    bound
  . unfold usq square
    simp [AffineIsometryEquiv.constVAdd,homothety]
    simp [← and_assoc,h']
    bound
  . unfold usq square
    simp [rotLeft,AffineIsometryEquiv.constVAdd]
    simp [← and_assoc,h]
    bound

def rotCor (r : Rot) (c : Cor) : Cor := match r with
  | Rot.none => c
  | Rot.left => match c with
    | Cor.bl => Cor.br
    | Cor.br => Cor.tr
    | Cor.tr => Cor.tl
    | Cor.tl => Cor.bl
  | Rot.half => match c with
    | Cor.bl => Cor.tr
    | Cor.br => Cor.tl
    | Cor.tr => Cor.bl
    | Cor.tl => Cor.br
  | Rot.right => match c with
    | Cor.bl => Cor.tl
    | Cor.br => Cor.bl
    | Cor.tr => Cor.br
    | Cor.tl => Cor.tr

/-
theorem rcor_consistent {rot : Rot} {cor : Cor} :
  rotTransform rot '' (corTransform cor '' usq) = corTransform (rcor rot cor) '' usq := by
  sorry-/
