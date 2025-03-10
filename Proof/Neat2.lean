import Mathlib
open Set
open OrderHom

macro "R2" : term => `(ℝ × ℝ)
--def R2 := ℝ × ℝ

@[simp]
def d0 (p : R2) := ((p.1 - p.2) * (0.5 : ℚ ) , (p.1 + p.2) * 0.5 + 1 )

@[simp]
def d1 (p : R2) := ((p.1 + p.2 + 1) * 0.5 , (p.2 - p.1 + 3) * 0.5)

example : d0 (-1,1) = (-1,1) := by
  rw [Prod.eq_iff_fst_eq_snd_eq]
  --apply (Iff.mpr Prod.eq_iff_fst_eq_snd_eq)
  apply And.intro
  unfold d0
  norm_num
  unfold d0
  simp

example : d1 (2,1) = (2,1) := by
  rw [Prod.eq_iff_fst_eq_snd_eq]
  apply And.intro
  . unfold d1
    norm_num
  . unfold d1
    norm_num

--  (f : a →o (b → c)) x : b →o c

def unit_sq : Set R2 := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 }

def treeFun (s : Set R2) : Set R2 := d0 '' s ∪ d1 '' s ∪ unit_sq

theorem constx_mono {β} {x:α} [Preorder α] [Preorder β]: Monotone (Function.const β x) := by
  intro _ _ _
  rfl

#print constx_mono

theorem fcdef  {β} {x:α} : Function.const β x = fun _ ↦ x := by
  rfl
theorem treeFun_monotone : Monotone (treeFun) := Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const
--)(fun {α} {β} {x} [Preorder α] [Preorder β] ⦃a b⦄ a_1 ↦ le_refl (Function.const β x a))

--(le_refl (fun _ (x:R2) _ => x))
/-by
  apply (Monotone.sup (Monotone.sup monotone_image monotone_image))
  exact constx_mono-/


#print treeFun_monotone
theorem treeFun_monotone2 : Monotone (treeFun) := by
  -- unfold Monotone
  intro a b hh
  apply sup_le
  apply sup_le
  unfold treeFun
  -- aesop [monotone_image hh, le_sup_left,le_sup_right, le_trans]
  calc d0 '' a ≤ d0 '' b := monotone_image hh
       _ ≤ d0 '' b ∪ d1 '' b := le_sup_left
       _ ≤ treeFun b := le_sup_left
  calc d1 '' a ≤ d1 '' b := monotone_image hh
       _ ≤ d0 '' b ∪ d1 '' b := le_sup_right
       _ ≤ treeFun b := le_sup_left
  exact le_sup_right
def treeFun_m : Set R2 →o Set R2 := ⟨ treeFun , treeFun_monotone⟩

def pythagTree := lfp treeFun_m

theorem sq_in_pyt :  unit_sq ⊆ pythagTree := by
  unfold pythagTree
  rw [← map_lfp treeFun_m]
  exact (le_sup_right)

def pythag_rect : Set R2 := {⟨ x , y ⟩ | -3<x ∧ x<4 ∧ 0<y ∧ y<4 }

variable [CompleteLattice α] [CompleteLattice β] (f : α →o α)

open fixedPoints

theorem lfp_f_eq_lfp_ff : lfp f = lfp (f.comp f) := by
  unfold lfp
  apply le_antisymm
  .
    simp
    intro b h
    have lem : f (b ⊓ f b ) ≤ b ⊓ f b := by
      apply le_inf
      --rel [f.mono,inf_le_right]
      --rel [_]
      transitivity f (f b)
      have k := @inf_le_right
      mono
      --rel [f.mono , @inf_le_right α _ b (f b) ]
      --apply f.mono
      --exact @inf_le_right α _ b (f b)
      trivial
      apply f.mono
      exact inf_le_left
    transitivity (b ⊓ f b)
    transitivity f (b ⊓ f b )
    apply sInf_le
    rw [mem_setOf_eq]
    apply f.mono
    exact lem
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
open Real


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
macro "rw_pair2" i:(ident) : tactic =>
    `(tactic| (
        simp at $i
        apply Prod.eq_iff_fst_eq_snd_eq.mp at $i
      --  try apply eq_iff_fst_eq_snd_eq.mp at $i
        simp at $i
        rw [← ($i).left, ← ($i).right]
      ))

theorem pyt_in_rect : pythagTree ⊆ pythag_rect := by
  unfold pythagTree
  rw [lfp_f_eq_lfp_ff]
  apply (@lfp_induction _ _ (treeFun_m.comp treeFun_m) (fun x => x ⊆ pythag_rect))
  . intro a h _ ⟨x,y⟩ ht
    unfold pythag_rect
    simp
    cases' ht with q q
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      rw_pair rr
      cases' q with q q
      cases' q with q q <;>
        (
        obtain ⟨ ⟨x,y ⟩ ,⟨q,rr⟩ ⟩ := q
        rw_pair rr
        apply h at q
        unfold pythag_rect at q
        simp at q
        norm_bound
        )
      unfold unit_sq at q
      simp at q
      norm_bound
      )
    unfold unit_sq at q
    simp at q
    bound
  intro s
  exact sSup_le

theorem pyt_area : MeasureTheory.volume pythagTree = 12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979 / 877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
 := by
  sorry


def pythag_rect2 : Set R2 := {⟨ x , y ⟩ | -2.5<x ∧ x<3.5 ∧ 0<y ∧ y<4 }

theorem pyt_in_rect2 : pythagTree ⊆ pythag_rect2 := by
  unfold pythagTree
  rw [lfp_f_eq_lfp_ff]
  apply (@lfp_induction _ _ (treeFun_m.comp treeFun_m) (fun x => x ⊆ pythag_rect2))
  . intro a h _ ⟨x,y⟩ ht
    unfold pythag_rect2
    norm_num
    --simp
    cases' ht with q q
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      rw_pair rr
      cases' q with q q
      cases' q with q q <;>
        (
        obtain ⟨ ⟨x,y ⟩ ,⟨q,rr⟩ ⟩ := q
        rw_pair rr
        apply h at q
        unfold pythag_rect2 at q
        simp at q
        norm_num at q
        norm_bound
        )
      unfold unit_sq at q
      simp at q
      norm_bound
      )
    unfold unit_sq at q
    simp at q
    bound
  intro s
  exact sSup_le
