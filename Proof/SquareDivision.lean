import Mathlib

open Real
open AffineMap
open Matrix
open Prod
open MeasureTheory
open Set

--  namespace SquareDiv

macro "R2" : term => `(ℝ × ℝ)


def rect (c : ℝ × ℝ ) (w:ℝ) (h : ℝ) := Ioo c.1 (c.1+w) ×ˢ Ioo c.2 (c.2+h)

def square (c :ℝ×ℝ) (sz : NNReal) := Ioo c.1 (c.1+sz) ×ˢ Ioo c.2 (c.2+sz)

def usq : Set (ℝ×ℝ)  := square ⟨0, 0⟩ 1

def irect (n : ℕ ) (m : ℕ) : Type := (Fin n × Fin m)

-- s1 : ℤ ⨯ ℤ

lemma pairne {A B : Type} {p q : A × B } (h : p ≠ q) : p.1≠ q.1 ∨ p.2 ≠ q.2 := by
  simp [Prod.ext_iff] at h
  -- simp
  rw [← imp_iff_not_or]
  trivial

theorem usqs_divide_rect (n : ℕ ) (m : ℕ) :
  PairwiseDisjoint (⊤ : Set (Fin n × Fin m)) (fun (i,j) => square ⟨i,j⟩ 1 ) := by
  intro ⟨i,j⟩
  intro _
  intro ⟨x,y⟩
  intro _
  intro ne
  apply pairne at ne
  simp at ne
  intro s ina inb p pins
  simp
  simp at ina inb
  apply mem_of_mem_of_subset pins at ina
  apply mem_of_mem_of_subset pins at inb
  cases' ne with ne ne <;>(
    simp at ne
    have ne:= mt Fin.eq_of_val_eq ne
    cases' Nat.lt_or_gt_of_ne ne with lt lt <;> (
      have ilx1 := (Nat.le_sub_one_of_lt lt)
      obtain ⟨a,b⟩  :=p
      unfold square at ina inb
      simp at ina inb
      -- rw [← Nat.cast_le] at ilx1
      have ilx1 : (_: ℝ) ≤ _ := Nat.cast_le.mpr ilx1
      rw [Nat.cast_sub (Nat.one_le_of_lt lt)] at ilx1
      simp at ilx1
      bound
    )
  )

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



/-
theorem corners_disj : Pairwise (Disjoint on (λ c:Cor => corTransform c '' unit_sq ) ) := sorry
-/
/-

-- inductive Piece : Type
  | triangle :  Piece -- triangle is bottom left half of unit_sq
  | emptyPiece : Piece
  | fullPiece : Piece

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
  . ext p : 2 <;>(
      simp_all only [LinearMap.coe_toAffineMap, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
        smul_fst, smul_snd, smul_eq_mul,
        coe_add, coe_smul, coe_sub, coe_id, coe_const, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        Function.const_apply,
        fst_add, fst_sub, fst_mul, snd_add,snd_sub, snd_mul, fst_ofNat, mul_zero, sub_zero, add_zero]
    )
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


-- Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1
-- def unit_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 }
/-

theorem unit_sq_eq_usq : unit_sq = usq := by
  ext ⟨x,y⟩
  unfold unit_sq
  unfold usq
  unfold square
  simp_all only [mem_setOf_eq, NNReal.coe_one, zero_add, mem_prod, mem_Ioo]
  bound
-/
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
theorem sq_cors {c : ℝ×ℝ} {sz : NNReal} {i : Cor} : corTransform i '' (square c sz) = (square (corTransform i c) (sz /2)) := by
  obtain ⟨c1,c2⟩  := c
  unfold corTransform
  unfold square
  unfold image
  cases i <;> (
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
  )

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

theorem cor_disj : Pairwise (Function.onFun Disjoint (fun i ↦ ⇑(corTransform i) '' usq)) := by
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

theorem square_has_4_corners : Fintype.card Cor = 4 := by
  rfl

--  end SquareDiv
