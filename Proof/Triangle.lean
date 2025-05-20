import Mathlib
import Proof.SquareDivision
import Proof.Pieces

def triangle : Set (ℝ×ℝ) := {⟨x,y⟩  | 0<x ∧ 0<y ∧  x+y<1}


lemma tri_in_sq : triangle ⊆ usq := by
  unfold triangle usq square
  intro ⟨ x,y⟩
  simp
  bound

/-
def triangleMap (cor : Cor) : Piece := match cor with
  | .bl => fullPiece
  | .tr => emptyPiece
  | _ => trianglePiece Rot.none
-/
-- theorem triMap_makes_tri (cor : Cor): triangle ∩ (corTransform cor '' usq) = (corTransform cor '' triangle) := by


theorem tri_tl : triangle ∩ (corTransform Cor.tl '' usq) = (corTransform Cor.tl '' triangle) := by
  unfold usq
  rw [sq_cors]
  ext ⟨ x,y⟩
  simp only [corTransform]
  unfold triangle square
  have h1 {a b:ℝ }:2⁻¹ * a = b ↔ a = 2*b := by norm_num; bound
  have h2 {a b:ℝ }:2⁻¹ * a + 2⁻¹ = b ↔ a = 2*b - 1 := by norm_num; bound
  simp [h1,h2]
  norm_num
  apply Iff.intro <;>(
    intro h
    and_intros <;> linarith
  )
theorem tri_br : triangle ∩ (corTransform Cor.br '' usq) = (corTransform Cor.br '' triangle) := by
  unfold usq
  rw [sq_cors]
  ext ⟨ x,y⟩
  simp only [corTransform]
  unfold triangle square
  simp [(by norm_num; bound : ∀ a b : ℝ , 2⁻¹ * a = b ↔ a = 2*b)]
  simp [(by norm_num; bound : ∀ a b : ℝ , 2⁻¹ * a + 2⁻¹ = b ↔ a = 2*b - 1)]
  norm_num
  apply Iff.intro <;>(
    intro h
    and_intros <;> linarith
  )
theorem tri_bl : triangle ∩ (corTransform Cor.bl '' usq) = (corTransform Cor.bl '' usq) := by
  unfold usq
  rw [sq_cors]
  ext ⟨ x,y⟩
  simp only [corTransform]
  simp [triangle,square]
  norm_num
  intros
  and_intros <;> linarith
theorem tri_tr : triangle ∩ (corTransform Cor.tr '' usq) = ∅ := by
  apply Set.eq_empty_of_forall_not_mem
  intro ⟨ x,y⟩
  rw [corTransform]
  simp [triangle,usq,square]
  norm_num
  intros
  linarith
