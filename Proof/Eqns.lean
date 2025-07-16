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

def qFull:  ℚ := 12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979/877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
def qEmpty:  ℚ := 11746934357449947552830291532943152290456105411186011016486060686616960007897677336844906536622212814156785625/877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
