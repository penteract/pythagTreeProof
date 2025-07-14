import Mathlib
-- import Proof.Eqns
@[irreducible]
def l := List.range (3000000)

-- #eval allparts'

theorem thm : l ≠ [] := by


#check ((List.head_mem (List.range_ne_nil.mpr sorry)) : l.head sorry ∈ l.toFinset)
