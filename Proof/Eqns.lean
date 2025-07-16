import Mathlib

-- Stuff needed by ProofCert.lean and also by other files

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



def fromAllParts : (α× (List α) × ℚ) → (List (α × ℚ) × ℚ)  := (fun x ↦
          match x with
          | (a, b, q) => ((a, 4) :: List.map (fun x ↦ (x, -1)) b, q))
