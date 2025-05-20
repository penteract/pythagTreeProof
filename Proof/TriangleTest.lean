import Mathlib
import Proof.SquareDivision
import Proof.Basic
open OrderHom
open Real
open ENNReal
open NNReal
open Set

open Lean.Parser.Tactic
open Lean

-- macro "norm_bound" : tactic => `(tactic| (norm_num ; bound))

-- minimal setup for theorem statement (does not depend on SquareDiv)
def d0 (p : (ℝ × ℝ)) := (p.1*0.5, p.2*0.5+0.5)

def d1 (p : (ℝ × ℝ)) := (p.1*0.5+0.5, p.2*0.5)

def cor_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<0.5 ∧ 0<y ∧ y<0.5 }

def triFun (s : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := d0 '' s ∪ d1 '' s ∪ cor_sq

theorem triFun_monotone : Monotone (triFun) := Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const
def triFun_m : Set (ℝ × ℝ) →o Set (ℝ × ℝ) := ⟨ triFun , triFun_monotone⟩

-- technically not a triangle (missing some lines (x,a\*2^-n) and (a\*2^-n,y))
def triangle := lfp triFun_m

/-
-- Main theorem
theorem tri_area : MeasureTheory.volume triangle = 1 / 2
 := by
  sorry
-/
-- Proof
--  open SquareDiv

lemma cor_sq_eq_square : cor_sq = square (0,0) (1/2) := by
  unfold square cor_sq
  ext ⟨ x,y⟩
  norm_num
  bound


lemma d1_br : d1 = corTransform Cor.br := by
  unfold d1
  ext x <;>(
    simp [corTransform]
    norm_num
    bound
  )
lemma d0_tl : d0 = corTransform Cor.tl := by
  unfold d0
  ext x <;>(
    simp [corTransform]
    norm_num
    bound
  )

theorem d0homothety : d0  = (AffineMap.homothety (0 ,1)  (0.5 : ℝ ) ) := by
  rw [d0_tl]
  rw [corTransform_homothety]
  simp [corTransform,Prod.mul_def]
  norm_num

theorem ar_quater (s : Set (ℝ×ℝ) ) : MeasureTheory.volume (d0 '' s) = MeasureTheory.volume s /4 := by
  rw [d0homothety]
  rw [MeasureTheory.Measure.addHaar_image_homothety]
  simp
  norm_num
  rw [ENNReal.ofReal_div_of_pos]
  norm_num
  rw [mul_comm]
  rfl
  simp

theorem d0_affine_equiv : d0 = (AffineEquiv.homothetyUnitsMulHom (0,1)) (Units.mk0 (0.5:ℝ) (by norm_num)) := by
  simp [AffineEquiv.coe_homothetyUnitsMulHom_apply,d0homothety]

theorem d1homothety : d1  = (AffineMap.homothety (1 ,0)  (0.5 : ℝ ) ) := by
  rw [d1_br]
  rw [corTransform_homothety]
  simp [corTransform,Prod.mul_def]
  norm_num

theorem d1_affine_equiv : d1 = (AffineEquiv.homothetyUnitsMulHom (1,0)) (Units.mk0 (0.5:ℝ) (by norm_num)) := by
  simp [AffineEquiv.coe_homothetyUnitsMulHom_apply,d1homothety]

theorem ar_quater1 (s : Set (ℝ×ℝ) ) : MeasureTheory.volume (d1 '' s) = MeasureTheory.volume s /4 := by
  rw [d1homothety]
  rw [MeasureTheory.Measure.addHaar_image_homothety]
  simp
  norm_num
  rw [ENNReal.ofReal_div_of_pos]
  norm_num
  rw [mul_comm]
  rfl
  simp

lemma d1_preserve_measurable {s: Set (ℝ × ℝ)} (h : MeasurableSet s) : MeasurableSet (d1 '' s) := by
  rw [d1_affine_equiv]
  exact (affine_measurable _ h)
lemma d0_preserve_measurable {s: Set (ℝ × ℝ)} (h : MeasurableSet s) : MeasurableSet (d0 '' s) := by
  rw [d0_affine_equiv]
  exact (affine_measurable _ h)
theorem triFun_measure_preserving {s : Set (ℝ×ℝ)} (h : MeasurableSet s) : MeasurableSet (triFun s) := by
  unfold triFun
  apply MeasurableSet.union
  apply MeasurableSet.union
  exact (d0_preserve_measurable h)
  exact (d1_preserve_measurable h)
  rw [cor_sq_eq_square]
  exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo


theorem triangle_measurable: MeasurableSet triangle := by
  unfold triangle
  rw [fixedPoints.lfp_eq_sSup_iterate]
  unfold iSup
  apply MeasurableSet.iUnion
  intro n
  induction n with
   | zero => simp
   | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (triFun_measure_preserving ih)
  unfold triFun_m
  unfold OmegaCompletePartialOrder.Continuous
  unfold CompleteLattice.instOmegaCompletePartialOrder
  simp
  intro c
  ext x
  unfold triFun
  repeat rw [image_iUnion]
  simp only [mem_union,mem_iUnion,exists_or,exists_const]


def triCor (c : Cor) : Set (ℝ×ℝ) := match c with
  | Cor.bl => usq
  | Cor.br => triangle
  | Cor.tl => triangle
  | Cor.tr => ∅


lemma obv2 (a:ENNReal ): a/4*2 = a/2 := by
  cases a
  rw [top_div]
  simp_all only [ite_mul, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, top_mul]
  split
  contradiction
  rw [top_div]
  simp_all only [ofNat_ne_top, ↓reduceIte]
  have h4 : (4 :ENNReal) = ↑(4 : NNReal) := (coe_ofNat 4)
  have h2 : (2 :ENNReal) = ↑(2 : NNReal) := (coe_ofNat 2 )
  rw [h4, h2 , ←ENNReal.coe_div , ←ENNReal.coe_div , ←ENNReal.coe_mul]
  apply ENNReal.coe_inj.mpr
  ext1
  simp_all only [coe_ofNat, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  bound
  exact (OfNat.ofNat_ne_zero 2)
  exact (OfNat.ofNat_ne_zero 4)


lemma tri_h : triangle = triFun triangle := by
  symm
  exact (OrderHom.map_lfp triFun_m)


variable (α : Type)
variable (a b c : Set α)

lemma tri_in_sq : triangle ⊆ usq := by
  apply (@lfp_induction _ _ (triFun_m) (fun x => x ⊆ usq))
  . intro a h _ ⟨x,y⟩ ht
    unfold usq square
    simp
    cases' ht with q q
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      obtain ⟨ aa,bb⟩ := rr
      apply h at q
      unfold usq square at q
      simp at q
      norm_num
      bound
      )
    unfold cor_sq at q
    simp at q
    norm_num at q
    bound

  intro s
  exact sSup_le

lemma cor_sq_eq_bl_usq : cor_sq = (corTransform Cor.bl) '' usq  := by
  unfold usq
  rw [sq_cors]
  rw [cor_sq_eq_square]
  unfold corTransform
  simp
lemma pairwise_empty_subset {a b : Cor} (h : a ≠ b) : corTransform a '' usq ∩ corTransform b '' usq = ∅ :=
          disjoint_iff_inter_eq_empty.mp (cor_disj h)
lemma tri_inter_sq_empty {a b : Cor} (h : a ≠ b) : corTransform a '' triangle ∩ corTransform b '' usq = ∅ :=
  subset_empty_iff.mp (Subset.trans
    (inter_subset_inter_left _ (image_mono tri_in_sq))
    (subset_empty_iff.mpr (pairwise_empty_subset h)))
lemma tri_cor_eq_triCor : (triangle ∩ ⇑(corTransform Cor.br) '' usq = ⇑(corTransform Cor.br) '' triCor Cor.br)
             ∧ (triangle ∩ ⇑(corTransform Cor.tl) '' usq = ⇑(corTransform Cor.tl) '' triCor Cor.tl)
  := by
  have h : triangle ⊆ usq := tri_in_sq
  apply And.intro <;> (
    -- simp only [← d0_tl,← d1_br]
    unfold triCor

    --unfold corTransform
    simp
    nth_rewrite 1 [tri_h]
    unfold triFun
    rw[d0_tl,d1_br]
    --simp only [← d0eq,← d1eq]
    rw [union_inter_distrib_right]
    rw [union_inter_distrib_right]
    apply subset_antisymm

    -- unfold image
    . rw [cor_sq_eq_bl_usq]
      --transitivity ∅
      --swap
      --exact empty_subset _
      simp
      .
        simp [tri_inter_sq_empty (by simp : Cor.br ≠ Cor.tl),
              tri_inter_sq_empty (by simp : Cor.tl ≠ Cor.br),
              pairwise_empty_subset (by simp : Cor.bl ≠ Cor.br),
              pairwise_empty_subset (by simp : Cor.bl ≠ Cor.tl)]
    . rw [inter_eq_left.mpr (image_mono h)]
      try exact (subset_trans subset_union_right subset_union_left)
      try exact (subset_trans subset_union_left subset_union_left)
    )

lemma triCor_corners (i : Cor) :
  triangle ∩ (fun i s ↦ ⇑(corTransform i) '' s) i usq = (fun i s ↦ ⇑(corTransform i) '' s) i (triCor i) := by
  cases i
  . unfold triCor
    simp only []
    apply inter_eq_right.mpr
    rw [tri_h]
    unfold triFun
    rw [← cor_sq_eq_bl_usq]
    simp
  . exact tri_cor_eq_triCor.1
  . exact tri_cor_eq_triCor.2
  . rw [tri_h]
    unfold triFun
    transitivity ∅
    swap
    unfold triCor corTransform
    simp
    apply subset_empty_iff.mp
    rw [union_inter_distrib_right,union_inter_distrib_right, d1_br, d0_tl,cor_sq_eq_bl_usq]
    ( apply union_subset
      apply union_subset <;>
        apply subset_trans (inter_subset_inter_left _ (image_mono tri_in_sq))
    )<;>(
      simp
      apply Set.disjoint_iff_inter_eq_empty.mp
      have h:=cor_disj
      simp_all [Pairwise,not_false_eq_true]
    )

lemma measurable_sq_corners (i:Cor) : MeasurableSet ((fun i s ↦ ⇑(corTransform i) '' s) i usq) := by
  simp
  unfold usq
  rw [sq_cors]
  unfold square
  exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo

lemma tri_area_lem : MeasureTheory.volume triangle = MeasureTheory.volume triangle / 2 + 1/4 := by
  have vol_usq : MeasureTheory.volume usq = 1 := by
    simp [usq,vol_sq]

  nth_rewrite 1 [volume_sum_pieces (S := usq) (A := triangle) (t:= fun i s => corTransform i '' s) triCor]
  rw [tsum_fintype]
  unfold Finset.univ
  simp [Cor.fintype]
  repeat rw [vol_quater]
  unfold triCor
  simp
  rw [vol_usq]
  norm_num
  let hh := obv2 (MeasureTheory.volume triangle)
  rw [← hh,add_comm]
  ring
  . rw [vol_usq]; exact one_lt_top
  . simp
    intro i
    rw [← image_subset_iff]
    unfold usq
    rw [sq_cors]
    cases i <;>(
      simp [corTransform, square]
      try (
        rw [prod_subset_prod_iff]
        apply Or.inl
        apply And.intro
      )
    )<;>(
      intro x
      simp
      norm_num
      bound
    )
  . simp
    unfold usq
    simp [sq_cors]
    simp [vol_sq]
    norm_num
    symm
    rw [square_has_4_corners]
    rw [← toNNReal_eq_one_iff]
    rw [Nat.cast_ofNat, ENNReal.toNNReal_mul, ENNReal.toNNReal_coe]
    rw [ENNReal.toNNReal_ofNat]
    rw [Real.toNNReal_div]
    simp
    simp
  . exact cor_disj
  . exact measurable_sq_corners
  . intro i
    rw [← triCor_corners i]
    apply MeasurableSet.inter
    exact triangle_measurable
    exact (measurable_sq_corners i)
  . exact tri_in_sq
  exact triCor_corners

theorem obv6 {a : ENNReal} (h1: a=a/2+1/4) (h2 :a<⊤) : a=1/2 := by
  cases' a with x
  contradiction
  rw [← coe_ofNat] at h1
  rw [← (coe_ofNat)] at h1
  rw [← ENNReal.coe_one] at h1
  rw [← ENNReal.coe_div] at h1
  rw [← ENNReal.coe_div] at h1
  rw [← ENNReal.coe_add] at h1
  rw [← (coe_ofNat)]
  rw [← ENNReal.coe_one]
  rw [← ENNReal.coe_div]
  apply ENNReal.coe_inj.mpr
  apply ENNReal.coe_inj.mp at h1
  apply NNReal.coe_inj.mp
  apply NNReal.coe_inj.mpr at h1
  simp at h1
  norm_num at h1
  simp
  norm_num
  bound
  simp
  simp
  simp

theorem tri_area : MeasureTheory.volume triangle = 1/2 := by
  apply obv6 tri_area_lem
  apply (MeasureTheory.measure_lt_top_of_subset tri_in_sq)
  rw [vol_usq]
  exact one_ne_top





#check volume_sum_pieces
