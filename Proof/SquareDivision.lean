import Mathlib

open Real
open AffineMap
open Matrix
open Prod
open MeasureTheory

macro "R2" : term => `(ℝ × ℝ)

namespace SquareDiv

def unit_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 }

inductive Cor : Type where
  | bl : Cor
  | br : Cor
  | tl : Cor
  | tr : Cor
  deriving DecidableEq

instance Cor.fintype : Fintype Cor := ⟨ ⟨ {bl,br,tl,tr}, by simp⟩ , fun x => by cases x <;> simp⟩

-- Tranformation (scale and translate) sending unit_sq to a corner of unitsq
noncomputable def corTransform (cor : Cor) : (R2 →ᵃ[ℝ] R2) := match cor with
  | Cor.bl => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
  | Cor.br => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (1/2,0))
  | Cor.tl => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (0,1/2))
  | Cor.tr => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (1/2,1/2))



/- theorem corners_disj : Pairwise (Disjoint on (λ c:Cor => corTransform c '' unit_sq ) ) := sorry -/

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
/-
theorem rinv_consistent : rotTransform r (rotTransform (rinv r) x) = x := by
  sorry

theorem thm_rot {rot:Rot}: rotTransform rot '' unit_sq = unit_sq := by
  unfold rotTransform
  /-cases' rot <;> (
    simp

  )-/
  sorry

theorem rcor_consistent {rot : Rot} {cor : Cor} : rotTransform rot '' (corTransform cor '' unit_sq) = corTransform (rcor rot cor) '' unit_sq := by sorry
-/

inductive Piece : Type
  | triangle :  Piece -- triangle is bottom left half of unit_sq
  | emptyPiece : Piece
  | fullPiece : Piece

/-
def pieces (s : Z2) (cor : Cor) : List (Piece) := sorry

def triangleMap (cor:Cor) : Piece := match cor with
  | Cor.bl => Piece.fullPiece
  | Cor.tr => Piece.emptyPiece
  | _ => Piece.triangle -/

theorem corTransform_homothety (i: Cor) : corTransform i = AffineMap.homothety (2 * (corTransform i (0,0))) (1/2 : ℝ ) := by
  cases i <;> (
    unfold corTransform
    simp
    unfold AffineMap.homothety
    simp_all only [vsub_eq_sub, vadd_eq_add]
  )
  . ext p : 2 <;>
      simp_all only [LinearMap.coe_toAffineMap, LinearMap.smul_apply, LinearMap.id_coe, id_eq, smul_snd, smul_eq_mul,
        coe_add, coe_smul, coe_sub, coe_id, coe_const, Function.const_zero, sub_zero, Pi.add_apply, Pi.smul_apply,
        Pi.zero_apply, add_zero]
  . ext p : 2 <;>
      simp
    norm_num
    bound
  . ext p : 2 <;>
      simp
    norm_num
    bound
  . ext p : 2 <;> (
      simp
      norm_num
      bound
    )

open Set

def square (c :ℝ×ℝ) (sz : NNReal) := Ioo c.1 (c.1+sz) ×ˢ Ioo c.2 (c.2+sz)

def usq : Set (ℝ×ℝ)  := square ⟨0, 0⟩ 1
-- Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1

theorem unit_sq_eq_usq : unit_sq = usq := by
  ext ⟨x,y⟩
  unfold unit_sq
  unfold usq
  unfold square
  simp_all only [mem_setOf_eq, NNReal.coe_one, zero_add, mem_prod, mem_Ioo]
  bound

theorem vol_sq {c : ℝ×ℝ } {sz : NNReal} : volume (square c sz) = Real.toNNReal (sz*sz) := by
  unfold square
  unfold volume
  unfold Measure.prod.measureSpace
  rw [Measure.prod_prod]
  rw [volume_Ioo,volume_Ioo]
  simp
  rw [←NNReal.coe_mul,←ENNReal.coe_mul, Real.toNNReal_coe]

theorem vol_usq: volume usq = 1 := by
  unfold usq
  rw [vol_sq]
  simp only [NNReal.coe_one, mul_one, toNNReal_one, ENNReal.coe_one]

theorem I_disj {x1 x2 : ℝ } {sz1 : NNReal} (le : x1 + sz1 ≤ x2) : Ioo x1 (x1 + ↑sz1) ∩ Ioo x2 (x2 + ↑sz2) = ∅ := by
  apply subset_empty_iff.mp
  unfold Ioo
  intro x
  simp_all only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false]
  bound

theorem sq_disj_x {c1 c2 : ℝ×ℝ} {sz1 sz2 : NNReal} (le : c1.1 + sz1 ≤ c2.1): Disjoint (square c1 sz1) (square c2 sz2) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  unfold square
  rw [prod_inter_prod]
  rw [I_disj le,empty_prod]
theorem sq_disj_y {c1 c2 : ℝ×ℝ} {sz1 sz2 : NNReal} (le : c1.2 + sz1 ≤ c2.2): Disjoint (square c1 sz1) (square c2 sz2) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  unfold square
  rw [prod_inter_prod]
  rw [I_disj le,prod_empty]

set_option maxHeartbeats 300000
theorem sq_cors {c  : ℝ×ℝ} {sz : NNReal} {i : Cor} : corTransform i '' (square c sz) = (square (corTransform i c) (sz /2)) := by
  obtain ⟨c1,c2⟩  := c
  unfold corTransform
  unfold square
  unfold image
  checkpoint (cases i <;> (
    simp
    --ext p
    ext ⟨ x,y⟩
    rw [mem_prod,mem_Ioo,mem_Ioo]
    rw [mem_setOf_eq]
    simp
    have h1 {a b:ℝ }:2⁻¹ * a = b ↔ a = 2*b := by norm_num; bound
    have h2 {a b:ℝ }:2⁻¹ * a + 2⁻¹ = b ↔ a = 2*b - 1 := by norm_num; bound
    have h3 {b:ℝ }:2⁻¹ = b ↔ 1 = 2*b := by norm_num; bound
    simp [h1,h2,h3]
    norm_num
    bound
    --rw [(by simp :  2⁻¹ * a = x ↔ a = 2*x )]
    --rw [eq_exists_right]
    /-calc (∃ a b, ((c.1 < a ∧ a < c.1 + ↑sz) ∧ c.2 < b ∧ b < c.2 + ↑sz) ∧ (2⁻¹ * a, 2⁻¹ * b) = (x, y))
       _ ↔ (∃ a b, ((c.1 < a ∧ a < c.1 + ↑sz) ∧ c.2 < b ∧ b < c.2 + ↑sz) ∧ (a, b) = (2*x, 2*y)) := by sorry
       _ ↔ (2⁻¹ * c.1 < (x, y).1 ∧ (x, y).1 < 2⁻¹ * c.1 + ↑sz / 2) ∧ 2⁻¹ * c.2 < (x, y).2 ∧ (x, y).2 < 2⁻¹ * c.2 + ↑sz / 2 := by sorry

    rw [exists_eq_right]
    cases
    simp
    norm_num
    bound
    -/
    -- simp
    -- norm_num
    -- bound
  ))

theorem vol_quater {x: Set R2} {cor : Cor} : MeasureTheory.volume (corTransform cor '' x) = MeasureTheory.volume x /4 := by
  rw [corTransform_homothety]
  rw [MeasureTheory.Measure.addHaar_image_homothety]
  simp
  norm_num
  rw [abs_of_nonneg]
  rw [ENNReal.ofReal_div_of_pos]
  rw [mul_comm]
  simp_all only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat, one_div]
  rfl
  simp
  simp

theorem cor_disj : Pairwise (Disjoint on fun i ↦ ⇑(corTransform i) '' usq) := by
  intro i j
  intro h
  --apply Set.disjoint_iff_inter_eq_empty.mpr
  --simp
  unfold usq
  simp [sq_cors]
  cases' i <;>
    cases' j <;> (
      first | contradiction | (
        unfold Function.onFun
        simp
        first |
          apply sq_disj_x
          simp [corTransform]
          done |
          apply sq_disj_y
          simp [corTransform]
          done |
          apply Disjoint.symm
          first |
            apply sq_disj_x
            simp [corTransform]
            done |
            apply sq_disj_y
            simp [corTransform]
        )
    )
/-
theorem test : False := by
  #check exists_eq_right
  sorry-/

theorem square_has_4_corners : Fintype.card Cor = 4 := by
  rfl

end SquareDiv
