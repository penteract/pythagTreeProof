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


@[simp]
noncomputable def conj (a b : R2 ≃ᵃ[ℝ] R2) := AffineEquiv.trans (AffineEquiv.trans b.symm a) b
@[simp]
noncomputable def Rot.none := AffineEquiv.refl ℝ R2
@[simp]
noncomputable def Rot.left := conj rotLeft.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv
@[simp]
noncomputable def Rot.half : (R2 ≃ᵃ[ℝ] R2) := AffineEquiv.homothetyUnitsMulHom (⟨1/2,1/2⟩ : R2) (-1)
@[simp]
noncomputable def Rot.right := conj rotLeft.symm.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv

open List

-- Tranformation (rotate about (1/2,1/2)) sending unit_sq to unitsq
noncomputable def Rot : Finset (R2 ≃ᵃ[ℝ] R2) := Finset.mk {
  Rot.none,
  Rot.left,
  Rot.half,
  Rot.right
  --AffineEquiv.refl ℝ R2,
  --conj rotLeft.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv,
  --AffineEquiv.homothetyUnitsMulHom (⟨1/2,1/2⟩ : R2) (-1),
  --conj rotLeft.symm.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv
} (by
  unfold Multiset.Nodup
  apply Nodup.of_map (fun f => f ⟨0,0⟩)
  simp
  simp [rotLeft,AffineIsometryEquiv.constVAdd, AffineIsometryEquiv.symm,Prod.ext_iff,homothety]
  norm_num
)

def f (x : Rot) : Rot := x


/-

-- inductive Rot : Type where
  | none : Rot
  | left : Rot
  | half : Rot
  | right : Rot

def rinv (r:Rot): Rot := match r with
  | Rot.left => Rot.right
  | Rot.right => Rot.left
  | _ => r
-/

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


theorem thm_rot {rot:Rot}: rot '' usq = usq := by
  have h (b:ℝ ) (z:ℝ) : 2⁻¹ + (2⁻¹ + -b) = z ↔ b = 1-z := by
    norm_num
    bound
  have h' (b:ℝ ) (z:ℝ) : 2⁻¹ - b + 2⁻¹ = z ↔ b = 1-z := by
    norm_num
    bound
  unfold Rot at rot
  obtain ⟨r,rh⟩ := rot
  simp
  rcases rh with ⟨⟩ | ⟨_,rh⟩
  simp
  rcases rh with ⟨⟩ | ⟨_,rh⟩
  ext ⟨x,y⟩
  unfold usq square
  simp [AffineIsometryEquiv.constVAdd,AffineIsometryEquiv.symm,rotLeft]
  simp [← and_assoc,h]
  bound
  rcases rh with ⟨⟩ | ⟨_,rh⟩
  ext ⟨x,y⟩
  unfold usq square
  simp [homothety]
  simp [← and_assoc,h']
  bound
  rcases rh with ⟨⟩ | ⟨_,rh⟩
  ext ⟨x,y⟩
  unfold usq square
  simp [AffineIsometryEquiv.constVAdd,AffineIsometryEquiv.symm,rotLeft]
  simp [← and_assoc,h]
  bound
  contradiction

def rotCor (r : Rot) (c : Cor) : Cor := match rot with
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
