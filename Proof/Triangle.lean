import Mathlib
import Proof.SquareDivision


def unit_sq : Set R2 := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 }

def triangle : Set (ℝ×ℝ) := {⟨x,y⟩  | 0<x ∧ 0<y ∧  x+y<1}
