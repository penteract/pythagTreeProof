import Mathlib

import Proof.SquareDivision

open Real
open AffineMap
open Matrix
open Prod
open MeasureTheory



noncomputable def rotLeft : R2 ≃ₗ[ℝ] R2 := by
  let ml : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1 ; 1, 0 ]
  let mr : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1 ; -1, 0 ]
  have hmlmr : ml*mr = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
  have hmrml : mr*ml = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
  exact Matrix.toLinOfInv (Basis.finTwoProd _) (Basis.finTwoProd _) hmlmr hmrml
  -- exact (Matrix.toLinearEquiv (Basis.finTwoProd _) m h)


macro "Rot" : term => `(ZMod 4)
-- def Rot := ZMod 4
/- Could define it like this, but proving that it's a group is a waste of time
inductive Rot : Type where
  | none : Rot
  | left : Rot
  | half : Rot
  | right : Rot
  deriving DecidableEq
-/
def Rot.none : Rot := 0
def Rot.left : Rot := 1
def Rot.half : Rot := 2
def Rot.right : Rot := 3

-- def rinv (r:Rot): Rot := -r
/- match r with
  | Rot.left => Rot.right
  | Rot.right => Rot.left
  | _ => r
-/

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
  | 0 => AffineEquiv.refl ℝ R2 --LinearMap.toAffineMap (LinearMap.id)
  | 1 => conj rotLeft.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv
  | 2 => AffineEquiv.homothetyUnitsMulHom ⟨1/2,1/2⟩ (-1)
  | 3 => conj rotLeft.symm.toAffineEquiv (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv



-- theorem rinv_consistent : rotTransform r (rotTransform (rinv r) x) = x := by
--   obtain ⟨x,y⟩ := x
--   cases' r <;>(
--     unfold rotTransform rinv
--     simp
--     )
--   . unfold rotLeft
--     simp [AffineIsometryEquiv.constVAdd, AffineIsometryEquiv.symm]
--   . unfold homothety
--     simp
--   unfold rotLeft
--   simp [AffineIsometryEquiv.constVAdd,AffineIsometryEquiv.symm]


theorem thm_rot {rot:Rot}: rotTransform rot '' usq = usq := by
  have h (b:ℝ ) (z:ℝ) : 2⁻¹ + (-b + 2⁻¹) = z ↔ b = 1-z := by
    norm_num
    bound
  have h' (b:ℝ ) (z:ℝ) : 2⁻¹ - b + 2⁻¹ = z ↔ b = 1-z := by
    norm_num
    bound
  ext ⟨x,y⟩
  fin_cases rot
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
/-
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
-/
-- lemma coe_toAffineEquiv_symm {k : Type u_1} {V₁ : Type u_6} {V₂ : Type u_7} [Ring k] [AddCommGroup V₁]
--          [AddCommGroup V₂] [Module k V₁] [Module k V₂]
--     (e : V₁ ≃ₗ[k] V₂)
--      : (e.toAffineEquiv).symm = (e.symm : V₂ → V₁) :=
--   rfl
theorem rotIsRotation (r : Rot):
  rotTransform r =
    conj (conj (rotation (Circle.exp (π * (r.val : ℝ ) / 2))).toAffineEquiv Complex.equivRealProdLm.toAffineEquiv) (AffineIsometryEquiv.constVAdd ℝ R2 (1/2,1/2)).toAffineEquiv := by
  have h : π * 3 / 2 = -(π / 2) + 2*π := by
    rw [mul_div_assoc]
    ring
  fin_cases r <;> simp only
  ext ⟨x,y⟩
  -- aesop_unfold
  simp_all only [rotTransform, AffineEquiv.refl_apply, conj, one_div,
    AffineIsometryEquiv.toAffineEquiv_symm, Nat.reduceAdd, Fin.zero_eta, ZMod.val_zero, CharP.cast_eq_zero, mul_zero,
    zero_div, Circle.exp_zero, map_one, AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv,
    LinearEquiv.coe_toAffineEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_one, id_eq,
    AffineEquiv.apply_symm_apply, AffineIsometryEquiv.apply_symm_apply]
  simp_all only [ rotTransform, AffineEquiv.refl_apply, conj, one_div,
    AffineIsometryEquiv.toAffineEquiv_symm, Nat.reduceAdd, Fin.zero_eta, ZMod.val_zero, CharP.cast_eq_zero, mul_zero,
    zero_div, Circle.exp_zero, map_one, AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv,
    LinearEquiv.coe_toAffineEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_one, id_eq,
    AffineEquiv.apply_symm_apply, AffineIsometryEquiv.apply_symm_apply]
  /-simp_all only [Fin.isValue, rotTransform, AffineEquiv.refl_apply, conj, one_div,
    AffineIsometryEquiv.toAffineEquiv_symm, Fin.val_zero, CharP.cast_eq_zero, mul_zero,
    zero_div, Circle.exp_zero, _root_.map_one, AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv,
    LinearEquiv.coe_toAffineEquiv, LinearIsometryEquiv.coe_toLinearEquiv, LinearIsometryEquiv.coe_one, id_eq,
    AffineEquiv.apply_symm_apply, AffineIsometryEquiv.apply_symm_apply]
  -/
  --simp only
  ext ⟨x,y⟩ <;> (
    simp only [ZMod.val]
    simp [rotLeft,AffineIsometryEquiv.constVAdd]
    simp [LinearEquiv.toAffineEquiv, AffineEquiv.symm]
  )
  ext ⟨ x,y⟩ <;>(
    simp only [ZMod.val]
    simp [rotLeft,AffineIsometryEquiv.constVAdd,homothety]
    simp [LinearEquiv.toAffineEquiv, AffineEquiv.symm]
    ring
  )
  ext ⟨x,y⟩ <;> (
    simp only [ZMod.val]
    simp [rotLeft,AffineIsometryEquiv.constVAdd]
    simp [←Complex.ofReal_natCast,←Complex.ofReal_ofNat, ←Complex.ofReal_mul, ←Complex.ofReal_div]
    simp [LinearEquiv.toAffineEquiv, AffineEquiv.symm]

    simp [h, Real.cos_add_int_mul_two_pi]
  )


def rotCor (r : Rot) (c : Cor) : Cor := match r with
  | 0 => c
  | 1 => match c with
    | Cor.bl => Cor.br
    | Cor.br => Cor.tr
    | Cor.tr => Cor.tl
    | Cor.tl => Cor.bl
  | 2 => match c with
    | Cor.bl => Cor.tr
    | Cor.br => Cor.tl
    | Cor.tr => Cor.bl
    | Cor.tl => Cor.br
  | 3 => match c with
    | Cor.bl => Cor.tl
    | Cor.br => Cor.bl
    | Cor.tr => Cor.br
    | Cor.tl => Cor.tr

-- def rotRot (r:Rot) (r':Rot) : Rot := lefts.symm (lefts r + lefts r')


/-
lemma lll : (5 : ℝ)  % (2.1 :ℝ ) = (0:ℝ ) := by
  sorry


lemma l (a b : ℝ ) : a * 2⁻¹ + b * 2⁻¹ ≡ (a + b) % 4 * 2⁻¹ [PMOD 2] := by
  rw [← right_distrib]
  simp_all only [ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
  AddCommGroup.mul_modEq_mul_right,
    div_inv_eq_mul]
  simp [AddComGroup.ModEq]
  sorry
-/
lemma lemFinSumZMod (n : Nat) (a b : Fin n): a + b ≡ (a + b : Fin n) [ZMOD n] := by
  rw [Lean.Omega.Fin.ofNat_val_add]
  rw [Int.ModEq.eq_1]
  symm
  exact Int.emod_emod_of_dvd _ (dvd_refl _)

theorem cexp (a b:Fin 4 ) : (Circle.exp (π * ((a + b : Fin 4)) / 2 )) = Circle.exp (π * a / 2 ) *Circle.exp (π * b / 2 ) := by
  symm
  calc Circle.exp (π * a / 2 ) *Circle.exp (π * b / 2 )
    _ = Circle.exp (π * a / 2  + π * b / 2 ) := Eq.symm (Circle.exp_add (π * a / 2) (π * b / 2))
    _ = Circle.exp (π * (a+b) / 2  ) := by rw [div_add_div_same,← left_distrib]
    _ = (Circle.exp (π * ((a + b) : Fin 4 ) / 2 )) := by
      apply Circle.exp_inj.mpr

      have h:=Real.pi_ne_zero
      simp_all
      have h' : 2 * π * 2 / π = 4 := by
        ring_nf
        simp_all
      rw [h']
      have h'' : (4:ℝ) = (4:ℕ) := by simp
      rw [h'',← Lean.Grind.CommRing.natCast_add]
      apply AddCommGroup.ModEq.natCast
      rw [Fin.val_add, Nat.ModEq.eq_1]
      symm
      exact (Nat.mod_mod_of_dvd _ (dvd_refl 4))

-- lemma aff_e (a b : P₁ ≃ᵃ[k] P₂): a=b ↔ (a:P_\) = b

theorem rotTransform_hom (r:Rot) (r':Rot) : rotTransform (r + r') = AffineEquiv.trans (rotTransform r)  (rotTransform r') := by
  rw [rotIsRotation]
  rw [rotIsRotation]
  rw [rotIsRotation]
  rw [conj_trans]
  rw [conj_trans]
  simp only [ZMod.val]
  rw [cexp]
  apply congrArg (fun x => conj x _)
  apply congrArg (fun x => conj x Complex.equivRealProdLm.toAffineEquiv)
  apply AffineEquiv.coeFn_inj.mp
  rw [AffineEquiv.coe_trans]
  simp only [LinearEquiv.coe_toAffineEquiv,LinearIsometryEquiv.coe_toLinearEquiv]
  ext p
  simp only [Function.comp,rotation_apply]
  nth_rw 2 [mul_comm]
  rw [Submonoid.coe_mul,mul_assoc]

theorem rotCor_hom (r:Rot) (r':Rot) : rotCor (r + r') = rotCor r ∘ rotCor r' := by
  ext c
  fin_cases r <;>  fin_cases r' <;> cases c <;> decide

/-theorem rotRot_assoc (r1 r2 r3) : rotRot r1 (rotRot r2 r3) = rotRot (rotRot r1 r2) r3 := by
  cases r1 <;> cases r2 <;> cases r3 <;> simp [rotRot]-/

/-
theorem rcor_consistent {rot : Rot} {cor : Cor} :
  rotTransform rot '' (corTransform cor '' usq) = corTransform (rcor rot cor) '' usq := by
  sorry-/

theorem t314 : (3:ZMod 4) + 1 = 0 := by
  rfl

lemma lvol {s : Set (ℝ ×ℝ) } : volume ((fun (a:ℝ×ℝ) ↦         (2⁻¹, 2⁻¹) + a) '' s) = volume s := by
  simp only [Set.image_add_left, neg_mk, measure_preimage_add]

lemma add_stuff [Add α ] {a:α } : (fun x => a + f x) = (fun x => a+x) ∘ f := by
  ext x
  simp
lemma stuff_add {α} [Add α ] {f : α→α} {a:α } : (fun x => f (a+x)) = f ∘ (fun x => a+x) := by
  ext x
  simp


lemma lfun (f : α → α ) : f = fun x => f x := by
  rfl

theorem rot_vol_l : MeasureTheory.volume s = MeasureTheory.volume (rotTransform Rot.left '' s) := by
  simp only [rotTransform, «Rot».left, conj, one_div, AffineIsometryEquiv.toAffineEquiv_symm,
     AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv, LinearEquiv.coe_toAffineEquiv,
     AffineIsometryEquiv.coe_constVAdd, vadd_eq_add]
  rw [add_stuff,Set.image_comp]
  rw [lvol]
  simp only [AffineIsometryEquiv.symm, AffineIsometryEquiv.constVAdd, AffineEquiv.constVAdd_symm,
    neg_mk, AffineIsometryEquiv.coe_mk, AffineEquiv.constVAdd_apply, vadd_eq_add, map_add]
  rw [add_stuff,Set.image_comp]
  simp only [Set.image_add_left, neg_mk, measure_preimage_add]

  rw [lfun (DFunLike.coe rotLeft)]
  unfold rotLeft
  simp only [toLinOfInv_apply]
  rw [MeasureTheory.Measure.addHaar_image_linearMap]
  simp



--  Real.map_linearMap_volume_pi_eq_smul_volume_pi
theorem rot_vol : MeasureTheory.volume s = MeasureTheory.volume (rotTransform r '' s) := by
  fin_cases r
  simp only [rotTransform, AffineEquiv.refl_apply, Set.image_id']
  exact rot_vol_l
  simp
  nth_rw 2 [rot_vol_l]
  rw [← Set.image_comp]
  rw [← AffineEquiv.coe_trans]
  rw [← rotTransform_hom]
  simp [Rot.left,t314]
  /-
  rw [rotIsRotation]
  unfold conj
  --simp? [-rotation_apply]
  simp? [-rotation_apply,-Complex.equivRealProdLm_apply,AffineIsometryEquiv.constVAdd]
  rw [add_stuff,Set.image_comp]
  rw [lvol]
  rw [@stuff_add _ _ (fun a ↦
        Complex.equivRealProdLm
          ((rotation (Circle.exp (π * r.cast / 2))) (Complex.equivRealProdLm.toAffineEquiv.symm a))) (-2⁻¹, -2⁻¹)]
  rw [Set.image_comp]
  --rw [lvol]
  --rw [measure_preimage_add]
  rw [Set.image_add_left, neg_mk, measure_preimage_add]

  have h := MeasureTheory.measurePreserving_add_left
  simp only [one_div, AffineIsometryEquiv.toAffineEquiv_symm, ZMod.natCast_val,
    AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv, LinearEquiv.coe_toAffineEquiv,
    LinearIsometryEquiv.coe_toLinearEquiv, Complex.equivRealProdLm_apply,
    AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, mk_add_mk]
  simp only [one_div, AffineIsometryEquiv.toAffineEquiv_symm, ZMod.natCast_val,
    AffineEquiv.trans_apply, AffineIsometryEquiv.coe_toAffineEquiv, LinearEquiv.coe_toAffineEquiv,
    LinearIsometryEquiv.coe_toLinearEquiv, rotation_apply, Circle.coe_exp, Complex.ofReal_div,
    Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.equivRealProdLm_apply, Complex.mul_re,
    Complex.mul_im, AffineIsometryEquiv.coe_constVAdd, vadd_eq_add, mk_add_mk]
-/
