import Mathlib
import Proof.SquareDivision

open Set
open OrderHom

--macro "R2" : term => `(ℝ × ℝ)

-- Coordinates within the 7 by 4 grid to make the mapping from Fin 7 × Fin 4 straightforward.
@[simp]
def d0 (p : ℝ×ℝ) := ((p.1 - p.2 + 3) * (0.5 ) , (p.1 + p.2 - 1) * 0.5)

@[simp]
def d1 (p : ℝ×ℝ) := ((p.1 + p.2 + 4) * 0.5 , (p.2 - p.1 + 6) * 0.5)

def treeFun (s : Set R2) : Set R2 := d0 '' s ∪ d1 '' s ∪ Ioo 3 4 ×ˢ Ioo 0 1

theorem constx_mono {α β} {x:α} [Preorder α] [Preorder β]: Monotone (Function.const β x) := by
  intro _ _ _
  rfl

theorem treeFun_monotone : Monotone (treeFun) := Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const

def treeFun_m : Set R2 →o Set R2 := ⟨ treeFun , treeFun_monotone⟩

def pythagTree := lfp treeFun_m

-- check d0 and d1 are doing something reasonable
example : d0 (3,0) = (3,1) := by
  rw [Prod.eq_iff_fst_eq_snd_eq]
  --apply (Iff.mpr Prod.eq_iff_fst_eq_snd_eq)
  apply And.intro
  unfold d0
  norm_num
  unfold d0
  norm_num

example : d1 (4,0) = (4,1) := by
  rw [Prod.eq_iff_fst_eq_snd_eq]
  apply And.intro
  . unfold d1
    norm_num
  . unfold d1
    norm_num


theorem sq_ss_pyt :  Ioo 3 4 ×ˢ Ioo 0 1 ⊆ pythagTree := by
  unfold pythagTree
  rw [← map_lfp treeFun_m]
  exact (le_sup_right)

noncomputable def rotEighthLeftShrink : R2 ≃ₗ[ℝ] R2 := by
  let ml : Matrix (Fin 2) (Fin 2) ℝ := !![0.5, -0.5 ; 0.5, 0.5 ]
  let mr : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 ; -1, 1 ]
  have hmlmr : ml*mr = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
    norm_num
  have hmrml : mr*ml = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
    norm_num
  exact Matrix.toLinOfInv (Basis.finTwoProd _) (Basis.finTwoProd _) hmlmr hmrml
noncomputable def rotEighthRightShrink : R2 ≃ₗ[ℝ] R2 := by
  let mr : Matrix (Fin 2) (Fin 2) ℝ := !![0.5, 0.5 ; -0.5, 0.5 ]
  let ml : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1 ; 1, 1 ]
  have hmrml : mr*ml = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
    norm_num
  have hmlmr : ml*mr = 1 := by
    simp [ml,mr, Matrix.mul_fin_two, Matrix.one_fin_two]
    norm_num
  exact Matrix.toLinOfInv (Basis.finTwoProd _) (Basis.finTwoProd _) hmrml hmlmr

noncomputable def d0aff : R2 ≃ᵃ[ℝ] R2 :=
  AffineEquiv.trans rotEighthLeftShrink.toAffineEquiv (AffineEquiv.constVAdd ℝ R2 (1.5,-0.5))

noncomputable def d1aff : R2 ≃ᵃ[ℝ] R2 :=
  AffineEquiv.trans rotEighthRightShrink.toAffineEquiv (AffineEquiv.constVAdd ℝ R2 (2,3))

theorem d0_eq_d0aff : d0 = d0aff := by
  ext ⟨x,y⟩ <;>(
    unfold d0 d0aff rotEighthLeftShrink
    simp
    norm_num
    bound)
theorem d1_eq_d1aff : d1 = d1aff := by
  ext ⟨x,y⟩ <;>(
    unfold d1 d1aff rotEighthRightShrink
    simp
    norm_num
    bound)


variable {α β} [CompleteLattice α] [CompleteLattice β] (f : α →o α)

theorem lfp_f_eq_lfp_ff : lfp f = lfp (f.comp f) := by
  unfold lfp
  apply le_antisymm
  .
    simp
    intro b h
    have lem : f (b ⊓ f b ) ≤ b ⊓ f b := by
      apply le_inf
      transitivity f (f b)
      exact (f.mono inf_le_right)
      trivial
      exact (f.mono inf_le_left)
    transitivity (b ⊓ f b)
    transitivity f (b ⊓ f b )
    apply sInf_le
    rw [mem_setOf_eq]
    exact (f.mono lem)
    exact lem
    exact inf_le_left
  .
    simp
    intro b h
    have : (f (f b)) ≤ b := by
      apply (le_trans _ h)
      exact (f.mono  h)
    apply sInf_le
    trivial

theorem d00 {x y : ℝ} : d0 (d0 (x,y) ) = ((5-y)*0.5, x*0.5) := by
  simp
  norm_num
  bound
theorem d01 {x y : ℝ} : d0 (d1 (x,y) ) = ((2+x)*0.5, (4+y)*0.5) := by
  simp
  norm_num
  bound
theorem d10 {x y : ℝ} : d1 (d0 (x,y) ) = ((5+x)*0.5, (4+y)*0.5) := by
  simp
  norm_num
  bound
theorem d11 {x y : ℝ} : d1 (d1 (x,y) ) = ((9+y)*0.5, (7-x)*0.5) := by
  simp
  norm_num
  bound

def pythag_rect : Set R2 := {⟨ x , y ⟩ | 0<x ∧ x<7 ∧ 0<y ∧ y<4 }

open Lean.Parser.Tactic
open Lean

instance : Coe (TSyntax `ident) (TSyntax ``locationHyp) where
  coe s := ⟨ (mkNode `Lean.Parser.Tactic.locationHyp
                  #[(mkNode `null #[s.raw] ),
                  (mkNode `null #[])])   ⟩
macro "rw_pair" i:(ident) : tactic =>
    `(tactic| (
      try (simp at $i ; apply Prod.eq_iff_fst_eq_snd_eq.mp at $i)
      try apply eq_iff_fst_eq_snd_eq.mp at $i
      try simp at $i
      rw [← ($i).left, ← ($i).right]
      ))

theorem pyt_in_rect : pythagTree ⊆ pythag_rect := by
  unfold pythagTree
  rw [lfp_f_eq_lfp_ff]
  apply (@lfp_induction _ _ (treeFun_m.comp treeFun_m) (fun x => x ⊆ pythag_rect))
  . intro a h _ ⟨x,y⟩ ht
    unfold pythag_rect
    simp
    cases' ht with q sq
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      cases' q with q sq
      cases' q with q q <;>
        (
        obtain ⟨ ⟨x',y' ⟩ ,⟨q,rr'⟩ ⟩ := q
        rw [← rr'] at rr
        simp only [d00,d01,d10,d11] at rr
        rw_pair rr
        apply h at q
        unfold pythag_rect at q
        simp at q
        norm_num
        bound
        )
      simp at sq
      rw_pair rr
      norm_num
      bound
      )
    simp at sq
    bound
  intro s
  exact sSup_le
