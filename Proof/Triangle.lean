import Mathlib
import Proof.SquareDivision
import Proof.Basic
open OrderHom
open Real
open   ENNReal
open NNReal
open Set

open Lean.Parser.Tactic
open Lean

-- macro "norm_bound" : tactic => `(tactic| (norm_num ; bound))

-- minimal setup for theorem statement (does not depend on SquareDiv)
def d0 (p : (ℝ × ℝ)) := (p.1*0.5, p.2*0.5+0.5)

-- ((p.1 - p.2) * 0.5 , (p.1 + p.2) * 0.5 + 1 )

def d1 (p : (ℝ × ℝ)) := (p.1*0.5+0.5, p.2*0.5)

-- def unit_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 } -->

def cor_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<0.5 ∧ 0<y ∧ y<0.5 }

def triFun (s : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := d0 '' s ∪ d1 '' s ∪ cor_sq


theorem triFun_monotone : Monotone (triFun) := Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const
def triFun_m : Set (ℝ × ℝ) →o Set (ℝ × ℝ) := ⟨ triFun , triFun_monotone⟩

def triangle := lfp triFun_m

/-
-- Main theorem
theorem tri_area : MeasureTheory.volume triangle = 1 / 2
 := by
  sorry

theorem cont_image {α : Type } {β : Type} {f : α → β} : OmegaCompletePartialOrder.Continuous (⟨image f,monotone_image⟩) := by
  unfold OmegaCompletePartialOrder.Continuous
  sorry
-/
-- Proof
open SquareDiv

lemma cor_sq_eq_square : cor_sq = square (0,0) (1/2) := by
  unfold square cor_sq
  ext ⟨ x,y⟩
  norm_num
  bound



theorem d0homothety : d0  = (AffineMap.homothety (0 ,1)  (0.5 : ℝ ) ) := by
  funext p
  obtain ⟨ x,y ⟩ := p
  unfold d0
  simp
  unfold AffineMap.homothety
  simp
  norm_num
  bound

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
  funext p
  obtain ⟨ x,y ⟩ := p
  unfold d1
  simp
  unfold AffineMap.homothety
  simp
  norm_num
  bound

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

  --unfold MeasurableEmbedding
  --simp [MeasurableEmbedding]

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
  --unfold OmegaCompletePartialOrder.ωSup
  unfold CompleteLattice.instOmegaCompletePartialOrder
  simp
  intro c
  ext x
  unfold triFun
  repeat rw [image_iUnion]
  simp only [mem_union,mem_iUnion,exists_or,exists_const]
  /-

  apply Iff.intro
  intro h
  rw [mem_iUnion]
  cases' h with h h
  cases' h with h h <;> (
    rw [image_iUnion] at h
    rw [mem_iUnion] at h
    obtain ⟨ i,h⟩ := h
    use i
    simp only [mem_union_left,mem_union_right,h]
  )
  use 0
  simp only [mem_union_left,mem_union_right,h]
  intro h
  rw [mem_iUnion] at h
  cases' h with h h
  cases' h with h h
  sorry-/



lemma obv3 {a:ℝ}: a/4*2 = a/2 := by
  bound

def triCor (c : Cor) : Set (ℝ×ℝ) := match c with
  | Cor.bl => usq
  | Cor.br => triangle
  | Cor.tl => triangle
  | Cor.tr => ∅
lemma obv4 {a : NNReal}{b : NNReal}  (h : a = b) : (↑a : ENNReal) = (↑b : ENNReal)  := by
  exact  (ENNReal.coe_inj.mpr h)

lemma obv2 (a:ENNReal ): a/4*2 = a/2 := by
  cases a
  rw [top_div]
  simp_all only [ite_mul, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, top_mul]
  split
  contradiction
  rw [top_div]
  simp_all only [two_ne_top, ↓reduceIte]
  have h4 : (4 :ENNReal) = ↑(4 : NNReal) := (coe_ofNat 4)
  have h2 : (2 :ENNReal) = ↑(2 : NNReal) := (coe_ofNat 2 )
  rw [h4]
  rw [h2]
  rw [←ENNReal.coe_div]
  rw [←ENNReal.coe_div]
  rw [←ENNReal.coe_mul]
  apply obv4
  ext1
  simp_all only [coe_ofNat, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  bound
  simp
  simp

theorem obv5 (x:ENNReal) : (x+x) = x*2 := by
  cases' x with x
  simp_all only [add_top, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, top_mul]
  rw [← coe_ofNat 2,← ENNReal.coe_add,← ENNReal.coe_mul]
  apply obv4
  apply NNReal.eq
  simp_all only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
  bound

lemma tri_h : triangle = triFun triangle := by
  symm
  exact (OrderHom.map_lfp triFun_m)

/-
lemma d1eq : d1 = (fun a ↦ (2⁻¹ : ℝ) • a + (2⁻¹, 0)) := by
  unfold d1
  ext x <;>(
    simp
    norm_num
    bound
  )
lemma d0eq : d0 = (fun a ↦ (2⁻¹ : ℝ) • a + (0,2⁻¹)) := by
  unfold d0
  ext x <;>(
    simp
    norm_num
    bound
  ) -/
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
/-
lemma cor_bl_sq : cor_sq = corTransform Cor.bl '' unit_sq := by
  ext ⟨ x,y⟩
  have h : ⇑(corTransform Cor.bl) = (fun (p : (ℝ × ℝ)) => (p.1*0.5, p.2*0.5)) := by
    ext ⟨a,b⟩ <;> (
      simp [corTransform]
      norm_num
      bound)
  rw [h]
  unfold cor_sq
  simp [unit_sq,cor_sq]
  norm_num
  sorry

  --bound
-/
variable (α : Type)
variable (a b c : Set α)

 -- lemma test (h: a ⊓ b ≤  ⊥) : (a = ⊥) := by aesop?
/-
instance : Coe (TSyntax `ident) (TSyntax ``locationHyp) where
  coe s := ⟨ (mkNode `Lean.Parser.Tactic.locationHyp
                  #[(mkNode `null #[s.raw] ),
                  (mkNode `null #[])])   ⟩
macro "rw_pair" i:(ident) : tactic =>
    `(tactic| (
      try (simp at $i ; apply Prod.eq_iff_fst_eq_snd_eq.mp at $i)
      try apply Prod.eq_iff_fst_eq_snd_eq.mp at $i
      try simp at $i
      rw [← ($i).left, ← ($i).right]
      )) -/

-- lemma fpreImim (f : ) : f ⁻¹' (f '' s
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
/-
lemma d1_disj_d0 : (d0 '' usq) ∩ (d1 '' usq) = ∅ := by
  ext  ⟨ x,y⟩
  simp [d0,d1,usq,square]
  norm_num
  bound
lemma cor_disj_d1 : (cor_sq) ∩ (d1 '' unit_sq) = ∅ := by
  ext ⟨ x,y⟩
  -- let h := not_mem_empty p
  simp [d0,d1,unit_sq,cor_sq]
  --norm_num
  norm_num
  bound
lemma cor_disj_d0 : (cor_sq) ∩ (d0 '' unit_sq) = ∅ := by
  ext ⟨x,y⟩
  simp [d0,d1,unit_sq,cor_sq]
  norm_num
  bound


lemma d0t_disj_d1 : (d0 '' triangle) ∩ (d1 '' unit_sq) = ∅ := by
  apply subset_empty_iff.mp
  --apply (inf_le_inf_right (d1 '' unit_sq))
  transitivity (d0 '' unit_sq) ∩ (d1 '' unit_sq)
  apply inter_subset_inter_left
  exact (image_mono tri_in_sq)
  rw [d1_disj_d0]
lemma d0_disj_d1t : (d1 '' triangle) ∩ (d0 '' unit_sq) = ∅ := by
  apply subset_empty_iff.mp
  --apply (inf_le_inf_right (d1 '' unit_sq))
  rw [inter_comm]
  transitivity (d0 '' unit_sq) ∩ (d1 '' unit_sq)
  apply inter_subset_inter_right
  exact (image_mono tri_in_sq)
  rw [d1_disj_d0]
-/
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
        /-by
          exact subset_empty_iff.mp (Subset.trans (inter_subset_inter_left _ (image_mono tri_in_sq)) (subset_empty_iff.mpr (pairwise_empty_subset h)))
          apply subset_empty_iff.mp (Subset.trans (inter_subset_inter_left _ (image_mono tri_in_sq)) (subset_empty_iff.mpr (pairwise_empty_subset h)))
                    --#check inter_subset_inter_left
          --simp [inter_subset_inter_left,image_mono tri_in_sq]
          exact
          -- exact (image_mono tri_in_sq
          -/
        simp [tri_inter_sq_empty (by simp : Cor.br ≠ Cor.tl),
              tri_inter_sq_empty (by simp : Cor.tl ≠ Cor.br),
              pairwise_empty_subset (by simp : Cor.bl ≠ Cor.br),
              pairwise_empty_subset (by simp : Cor.bl ≠ Cor.tl)]
      --simp [d0t_disj_d1, d0_disj_d1t, cor_disj_d1, cor_disj_d0]
    . rw [inter_eq_left.mpr (image_mono h)]
      try exact (subset_trans subset_union_right subset_union_left)
      try exact (subset_trans subset_union_left subset_union_left)
    )
/-
lemma tri_tr_empty : triangle ∩ ⇑(corTransform Cor.tr) '' usq = ∅ := by
  rw [tri_h]
  unfold triFun
  apply subset_empty_iff.mp
  sorry
-/

lemma triCor_corners (i : Cor) :
  triangle ∩ (fun i s ↦ ⇑(corTransform i) '' s) i usq = (fun i s ↦ ⇑(corTransform i) '' s) i (triCor i) := by
  --intro i
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
    --simp [Pairwise,Function.onFun] at cor_disj_unit_sq
    -- #check (h (Cor.tl≠ Cor.tr)
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
  -- #check volume_sum_pieces (S := usq) (A := triangle) (t:= fun i s => corTransform i '' s) triCor
  -- have cor_disj_unit_sq := cor_disj
  -- rw [← unit_sq_eq_usq] at cor_disj_unit_sq
  nth_rewrite 1 [volume_sum_pieces (S := usq) (A := triangle) (t:= fun i s => corTransform i '' s) triCor]
  rw [tsum_fintype]
  --simp
  --unfold Finset.sum
  --simp
  unfold Finset.univ
  simp [Cor.fintype]
  repeat rw [vol_quater]
  unfold triCor
  simp
  --norm_num
  rw [vol_usq]
  norm_num
  let hh := obv2 (MeasureTheory.volume triangle)
  rw [← hh,add_comm]
  --norm_num
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
      -- unfold Ioo
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
    rw [← toNNReal_eq_one_iff]
    rw [← NNReal.tsum_eq_toNNReal_tsum]

    -- let a := Real.toNNReal (1/4)
    -- have ha : a = Real.toNNReal (4⁻¹) := by simp [a]
    -- simp [← ha]
    rw [← NNReal.coe_inj,NNReal.coe_one,NNReal.coe_tsum]
    rw [Real.coe_toNNReal]
    rw [tsum_const (1/4)]
    simp
    rw [square_has_4_corners]
    simp
    simp
    /-
    simp [Cor]
    rw [← h1]
    have h3 : ↑(∑' (b : Cor), (1 / 4 : ENNReal).toNNReal) = ↑ ((∑' (b : Cor), (↑((1 / 4 : ENNReal).toNNReal) : ENNReal)).toNNReal) := by
      rw [← toNNReal_eq_toNNReal_iff']
      --something using h1???

    rw [(sorry : 1 = (1:ENNReal).toNNReal)]
    have h : ∑' (b : Cor), (( ↑(1 / 4 : ENNReal).toNNReal) : ENNReal) =
             (∑' (b : Cor), ↑((1/4) : ENNReal).toNNReal ) := by
             have h' := NNReal.tsum_eq_toNNReal_tsum (f:=fun (i:Cor) =>  (↑(1 / 4 : ENNReal).toNNReal))


             exact NNReal.tsum_eq_toNNReal_tsum (f:= )


    (↑(1 / 4 : ENNReal).toNNReal) := NNReal.tsum_eq_toNNReal_tsum (f:=fun (i:Cor) =>  (↑(1 / 4 : ENNReal).toNNReal))
    rw [h]
    symm
    transitivity (Nat.card Cor)*↑(1 / 4)
    apply tsum_const
    -/
  . exact cor_disj
  . exact measurable_sq_corners
  . intro i
    rw [← triCor_corners i]
    apply MeasurableSet.inter
    exact triangle_measurable
    exact (measurable_sq_corners i)
  . exact tri_in_sq
  exact triCor_corners
  /-
  intro i
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
    --simp [Pairwise,Function.onFun] at cor_disj_unit_sq
    -- #check (h (Cor.tl≠ Cor.tr)
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
    -/


    /-
      (first | apply union_subset | skip) <;> (
        sorry
      )-/

    /-
    intro x h
    cases' h with h h <;> (
      (first | cases' h with h h | skip) <;> (
        have h' := cor_disj
      )
    )

    intro x ⟨ h1,h2 ⟩
    --have  := h
    --simp [unit_sq,image] at
    calc

    simp [image_mono tri_in_sq]

    --unfold once triangle
-/

    /-
    #check (@lfp_induction _ _ triFun_m (fun s => unit_sq ⊆ ⇑(0.5 • LinearMap.id) ⁻¹' s))
    apply (@lfp_induction _ _ triFun_m (fun s => unit_sq ⊆ ⇑(0.5 • LinearMap.id) ⁻¹' s))
    intro a h1 h2
    unfold triFun_m
    unfold triFun
    simp
    -- ℝ×ℝ →ₗ ℝ×ℝ
    transitivity (⇑(((0.5 : ℝ) • LinearMap.id) : ℝ×ℝ →ₗ[ℝ] ℝ×ℝ) ⁻¹' cor_sq)
    unfold unit_sq
    intro p
    obtain ⟨ x,y⟩ := p
    intro H
    unfold cor_sq
    simp
    simp at H
    norm_num
    bound
    simp_all only [le_eq_subset, subset_union_right]
    -/

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

theorem tri_area_final : MeasureTheory.volume triangle = 1/2 := by
  apply obv6 tri_area_lem
  apply (MeasureTheory.measure_lt_top_of_subset tri_in_sq)
  rw [vol_usq]
  exact one_ne_top





#check volume_sum_pieces
