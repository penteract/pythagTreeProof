import Mathlib
import Proof.SquareDivision
import Proof.Basic
open OrderHom
open Real
open ENNReal
open NNReal
open Set
open SquareDiv

open Lean.Parser.Tactic
open Lean
/-
instance : Coe (TSyntax ``locationHyp) (TSyntax `ident) where
  coe s := match s.raw with
    | (Syntax.node info `Lean.Parser.Tactic.locationHyp
                  #[(Syntax.node info2 `null #[t]
                    --(Syntax.ident info "i".toSubstring' (addMacroScope mainModule `i scp) [])
                      ),
                  (Syntax.node info3 `null #[])])  => ⟨ t ⟩
    | _ => ⟨s⟩
-/


macro "norm_bound" : tactic => `(tactic| (norm_num ; bound))


def d0 (p : (ℝ × ℝ)) := (p.1*0.5, p.2*0.5+0.5)



-- ((p.1 - p.2) * 0.5 , (p.1 + p.2) * 0.5 + 1 )

def d1 (p : (ℝ × ℝ)) := (p.1*0.5+0.5, p.2*0.5)

-- def unit_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 } -->

def cor_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<0.5 ∧ 0<y ∧ y<0.5 }

def triFun (s : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := d0 '' s ∪ d1 '' s ∪ cor_sq

theorem constx_mono {β} {x:α} [Preorder α] [Preorder β]: Monotone (Function.const β x) := by
  intro _ _ _
  rfl

theorem triFun_monotone : Monotone (triFun) := Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const
def triFun_m : Set (ℝ × ℝ) →o Set (ℝ × ℝ) := ⟨ triFun , triFun_monotone⟩

def triangle := lfp triFun_m

theorem tri_area : MeasureTheory.volume triangle = 1 / 2
 := by
  sorry

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


theorem d1homothety : d1  = (AffineMap.homothety (1 ,0)  (0.5 : ℝ ) ) := by
  funext p
  obtain ⟨ x,y ⟩ := p
  unfold d1
  simp
  unfold AffineMap.homothety
  simp
  norm_num
  bound

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

lemma obv3 {a:ℝ}: a/4*2 = a/2 := by
  bound

def triCor (c : Cor) : Set (ℝ×ℝ) := match c with
  | Cor.bl => unit_sq
  | Cor.br => triangle
  | Cor.tl => triangle
  | Cor.tr => ∅
lemma obv4 {a : NNReal}{b : NNReal}  (h : a = b) : (↑a : ENNReal) = (↑b : ENNReal)  := by
  exact  (ENNReal.coe_inj.mpr h)

lemma obv2 (a:ENNReal ): a/4*2 = a/2 := by
  cases a
  rw [top_div]
  simp_all only [ite_mul, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, top_mul]
  aesop
  contradiction
  rw [top_div]
  aesop
  have h4 : (4 :ENNReal) = ↑(4 : NNReal) := (coe_ofNat 4)
  have h2 : (2 :ENNReal) = ↑(2 : NNReal) := (coe_ofNat 2 )
  rw [h4]
  rw [h2]
  rw [←ENNReal.coe_div]
  rw [←ENNReal.coe_div]
  rw [←ENNReal.coe_mul]
  apply obv4
  aesop
  have h :(↑ x : ℝ ) /4*2 = (↑ x : ℝ ) /2 := by bound
  ext1
  simp_all only [NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
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
  )

lemma d1_br : d1 = corTransform Cor.br := by
  simp [corTransform]
  exact d1eq
lemma d0_tl : d0 = corTransform Cor.tl := by
  simp [corTransform]
  exact d0eq

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
lemma tri_in_sq : triangle ⊆ unit_sq := by
  apply (@lfp_induction _ _ (triFun_m) (fun x => x ⊆ unit_sq))
  . intro a h _ ⟨x,y⟩ ht
    unfold unit_sq
    simp
    cases' ht with q q
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      obtain ⟨ aa,bb⟩ := rr
      apply h at q
      unfold unit_sq at q
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

lemma d1_disj_d0 : (d0 '' unit_sq) ∩ (d1 '' unit_sq) = ∅ := by
  ext  ⟨ x,y⟩
  simp [d0,d1,unit_sq]
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

lemma tri_h2 : (triangle ∩ ⇑(corTransform Cor.br) '' unit_sq = ⇑(corTransform Cor.br) '' triCor Cor.br)
             ∧ (triangle ∩ ⇑(corTransform Cor.tl) '' unit_sq = ⇑(corTransform Cor.tl) '' triCor Cor.tl)
  := by
  have h : triangle ⊆ unit_sq := tri_in_sq
  apply And.intro <;> (
    unfold triCor
    unfold corTransform
    simp
    nth_rewrite 1 [tri_h]
    unfold triFun

    simp only [← d0eq,← d1eq]
    rw [union_inter_distrib_right]
    rw [union_inter_distrib_right]
    apply subset_antisymm

    -- unfold image
    . simp [d0t_disj_d1, d0_disj_d1t, cor_disj_d1, cor_disj_d0]
    . rw [inter_eq_left.mpr (image_mono h)]
      try exact (subset_trans subset_union_right subset_union_left)
      try exact (subset_trans subset_union_left subset_union_left)
    )

lemma tri_tr_empty : triangle ∩ ⇑(corTransform Cor.tr) '' unit_sq = ∅ := by
  simp [corTransform,]


lemma tri_area_lem : MeasureTheory.volume triangle = MeasureTheory.volume triangle / 2 + 1/4 := by
  #check volume_sum_pieces (S := unit_sq) (A := triangle) (t:= fun i s => corTransform i '' s) triCor
  nth_rewrite 1 [volume_sum_pieces (S := unit_sq) (A := triangle) (t:= fun i s => corTransform i '' s) triCor]
  rw [tsum_fintype]
  simp
  --unfold Finset.sum
  --simp
  unfold Finset.univ
  simp [Cor.fintype]
  repeat rw [vol_quater]
  unfold triCor
  simp
  norm_num
  have h : MeasureTheory.volume unit_sq = 1 := by sorry
  rw [h]
  norm_num
  let hh := obv2 (MeasureTheory.volume triangle)
  rw [← hh,add_comm]

  ring
  intro i
  cases i
  . unfold triCor
    unfold corTransform
    simp
    unfold triangle
    transitivity (⇑(((0.5 :ℝ ) • LinearMap.id) : ℝ×ℝ →ₗ[ℝ] ℝ×ℝ) ⁻¹' (triFun_m ∅))
    simp [triFun_m,triFun,cor_sq]
    intro ⟨ x,y ⟩
    norm_num
    bound
    norm_num
    apply Set.preimage_mono
    apply OrderHom.map_le_lfp triFun_m (Set.empty_subset _)
  . exact tri_h2.1
  . exact tri_h2.2
  . rw [tri_h]
    unfold triFun
    transitivity ∅
    swap
    unfold triCor corTransform
    simp
    apply subset_empty_iff.mp
    have h := cor_disj
    simp [Pairwise,Function.onFun] at h
    -- #check (h (Cor.tl≠ Cor.tr)
    rw [union_inter_distrib_right,union_inter_distrib_right, d1_br, d0_tl,cor_bl_sq]
    ( apply union_subset
      apply union_subset <;>
        apply subset_trans (inter_subset_inter_left _ (image_mono tri_in_sq))
    )<;>(
      simp
      apply Set.disjoint_iff_inter_eq_empty.mp
      simp_all only [not_false_eq_true]
    )
  . sorry
  . sorry
  . sorry
  . exact cor_disj
  . sorry
  . sorry
  . exact tri_in_sq


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







#check volume_sum_pieces
