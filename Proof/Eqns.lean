import Mathlib
-- Stuff about manipulating a system of linear equations as types
open List

namespace Eqns

variable {α β : Type}
-- variable (ll : List (List (α × ℚ) × ℚ)) -- represents a list of equations and coefficients of said equations
-- variable (toEqn : β → List (α × ℚ) )
-- variable (f : α → ℝ )

def all_vars [DecidableEq α] (ll : List (List (α × ℚ) × ℚ)) : List α := dedup ((flatMap Prod.fst ll ).map Prod.fst)

-- def Mat (ll : List (List (α × ℚ) × ℚ)) := Matrix { e // e∈ ll} {v // v ∈ (all_vars ll)}  ℚ

/-
def getMat (ll : List (List (α × ℚ) × ℚ)) :  Matrix { e // e∈ ll} {v // v ∈ (all_vars ll)} ℚ := Matrix.of
  (fun e v => sum (e.val.fst.map (fun (a,q) =>if a=v then q else 0 )))
-/
def getMat [DecidableEq α] (ll : List (List (α × ℚ) × ℚ)) :  Matrix ll.toFinset (all_vars ll).toFinset ℚ := Matrix.of
  (fun e v => sum (e.val.fst.map (fun (a,q) =>if a=v then q else 0 )))



theorem mat_z {m n : Type } [Fintype m] [Fintype n] {A : Matrix m n ℝ} {x r : n → ℝ} {v : m → ℝ}
  (hAx : Matrix.mulVec A x = 0) (hqA : Matrix.vecMul v A = r) : dotProduct r  x = 0 := by
  rw [← hqA]
  rw [← Matrix.dotProduct_mulVec]
  rw [hAx]
  exact (dotProduct_zero _)

lemma ratCast_eq (a b : ℚ) : a = b ↔ (a : ℝ) = (b : ℝ) := by simp only [Rat.cast_inj]

theorem mq_cast_r {i : n} {v : m → ℚ } [Fintype m] : (Rat.cast :ℚ→ℝ ) (Matrix.vecMul v A i) = Matrix.vecMul (Rat.cast ∘ v) (Matrix.map A Rat.cast) i := by
  -- #check RingHom.map_vecMul (Rat.castHom ℝ)  A v i
  exact RingHom.map_vecMul (Rat.castHom ℝ) _ _ _


theorem finsetset_subtype_is_finset {s : Finset β} : { x // x ∈ s } = s := by
 rfl


theorem thmst {s : Finset β} (f : β → ℝ) :(f∘(↑) : s→ ℝ ) = (Subtype.restrict _ f : { x // x ∈ s } → ℝ ) := by
  rfl

-- Finset.sum
theorem thmdot {s : Finset β } (f g : β → ℝ) : dotProduct (f∘(↑) : s→ ℝ )  (g ∘ (↑)) =
    @Finset.sum β  ℝ _ s (fun x => f x * g x) := by
  unfold dotProduct
  simp only [Function.comp_apply]
  rw [Finset.sum_coe_sort s (fun x => f x * g x)]
  -- alternative proof:
  -- rw [← Finset.sum_coe_sort s (fun x => f x * g x)]
  -- rfl

theorem thmdot2 {s : Finset β } (f g : β  → ℝ) : dotProduct (Subtype.restrict _ f : s → ℝ ) (Subtype.restrict _ g : s→ ℝ) =
    @Finset.sum β ℝ _ s (fun x => f x * g x) := by
  rw [← Finset.sum_coe_sort s (fun x => f x * g x)]
  rfl
