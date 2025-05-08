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


-- @[simp]
-- noncomputable def conj (a b : R2 ≃ᵃ[ℝ] R2) := AffineEquiv.trans (AffineEquiv.trans b.symm a) b
@[simp]
noncomputable def conj [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
                       [Module k V₂]  [AddTorsor V₁ A] [AddTorsor V₂ B]
  (a : B ≃ᵃ[k] B) (b : B ≃ᵃ[k] A) : A ≃ᵃ[k] A :=
  AffineEquiv.trans (AffineEquiv.trans b.symm a) b

theorem conj_trans [Ring k] [AddCommGroup V₁] [AddCommGroup V₂] [Module k V₁]
                       [Module k V₂]  [AddTorsor V₁ A] [AddTorsor V₂ B]
  (a b: B ≃ᵃ[k] B) (c : B ≃ᵃ[k] A) :
  AffineEquiv.trans (conj a c) (conj b c) = conj (AffineEquiv.trans a b) c := by
  simp
  ext1 x
  simp_all only [AffineEquiv.trans_apply, AffineEquiv.symm_apply_apply]

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
@[simp]
def lefts : Rot ≃ Fin 4 where
  toFun := fun r => match r with
    | Rot.none => 0
    | Rot.left => 1
    | Rot.half => 2
    | Rot.right => 3
  invFun := fun n => match n with
    | 0 => Rot.none
    | 1 => Rot.left
    | 2 => Rot.half
    | 3 => Rot.right
  left_inv := by
    intro r
    cases r <;> rfl
  right_inv := by
    intro r
    fin_cases r <;> rfl

def fromLefts (n : Fin 4) : Rot := match n with
  | 0 => Rot.none
  | 1 => Rot.none
  | 2 => Rot.none
  | 3 => Rot.none
theorem rotIsRotation (r : Rot):
  rotTransform r =
    conj (conj (rotation (Circle.exp (π * ((lefts r : ℕ) : ℝ ) / 2))).toAffineEquiv Complex.equivRealProdLm.toAffineEquiv) (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv := by
  have h : π * ↑(↑(3:Fin 4):ℕ) / 2 = -(π / 2) + 2*π := by
    rw [(by rfl : (↑(3:Fin 4):ℕ) = (3 : ℕ))]
    rw [mul_div_assoc]
    ring
  cases r
  ext ⟨x,y⟩
  simp_all only [Fin.isValue, rotTransform, AffineEquiv.refl_apply, conj, one_div,
    AffineIsometryEquiv.toAffineEquiv_symm, lefts, Equiv.coe_fn_mk, Fin.val_zero, CharP.cast_eq_zero, mul_zero,
    zero_div, Circle.exp_zero, _root_.map_one, AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv,
    LinearEquiv.coe_toAffineEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_one, id_eq,
    AffineEquiv.apply_symm_apply, AffineIsometryEquiv.apply_symm_apply]
  simp
  ext ⟨x,y⟩ <;> (
    simp [rotLeft,AffineIsometryEquiv.constVAdd]
    simp [← Complex.ofReal_ofNat, ← Complex.ofReal_div]
    simp [LinearEquiv.toAffineEquiv, AffineEquiv.symm]
  )
  ext ⟨ x,y⟩ <;>(
    simp [rotLeft,AffineIsometryEquiv.constVAdd,homothety]
    simp [LinearEquiv.toAffineEquiv, AffineEquiv.symm]
    ring
  )
  ext ⟨x,y⟩ <;> (
    simp [rotLeft,AffineIsometryEquiv.constVAdd]
    simp [←Complex.ofReal_natCast,←Complex.ofReal_ofNat, ←Complex.ofReal_mul, ←Complex.ofReal_div]
    simp [LinearEquiv.toAffineEquiv, AffineEquiv.symm]

    simp [h, Real.cos_add_int_mul_two_pi]
  )


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

def rotRot (r:Rot) (r':Rot) : Rot := lefts.symm (lefts r + lefts r')


theorem cexp (a b:ℝ ) : (Circle.exp (π * ((a + b) %4) / 2 )) = Circle.exp (π * a / 2 ) *Circle.exp (π * b / 2 ) := by
  symm
  calc Circle.exp (π * a / 2 ) *Circle.exp (π * b / 2 )
    = Circle.exp (π * a / 2  + π * b / 2 ) := Eq.symm (Circle.exp_add _ _)
    _ = (Circle.exp (π * ((a + b) %4) / 2 )) := by
      rw [div_add_div_same,← left_distrib]
      -- #check Circle.instContinuousSMul
      -- apply Circle.exp_inj
      rw [Circle.exp_eq_exp]
      sorry

theorem rotRot_consistent (r:Rot) (r':Rot) : rotTransform (rotRot r r') = AffineEquiv.trans (rotTransform r)  (rotTransform r') := by
  rw [rotIsRotation]
  rw [rotIsRotation]
  rw [rotIsRotation]
  rw [conj_trans]
  rw [conj_trans]
  unfold rotRot
  rw [Equiv.rightInverse_symm]




/-
theorem rcor_consistent {rot : Rot} {cor : Cor} :
  rotTransform rot '' (corTransform cor '' usq) = corTransform (rcor rot cor) '' usq := by
  sorry-/
