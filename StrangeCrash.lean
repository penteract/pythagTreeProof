import Mathlib


set_option maxRecDepth 200000
-- this annotation avoids running out of stack space
@[irreducible]
def l := List.range (3000000)

#check ((List.head_mem (List.range_ne_nil.mpr sorry)) : l.head sorry ∈ l.toFinset)
