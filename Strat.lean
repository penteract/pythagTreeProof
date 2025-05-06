import Mathlib
import Proof.SquareDivision
open SquareDiv

/- An alternative strategy for the proof, making things explicit rather than indexes-/
def Rotations : Set (ℝ×ℝ)

def Piece : Finset (Set (ℝ×ℝ) ) := sorry

def pythagTree : Set (ℝ × ℝ) := sorry

def grid := Fin 7 × Fin 4

def sqr (c : grid): Set R2 := square ⟨c.1,c.2⟩  1

def tile (c:grid) : Piece
  := ⟨ AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨3-c.1, -c.2⟩ '' (pythagTree ∩ (sqr c)),
       sorry ⟩

theorem piecesMakeRotTiles : Piece = { {⟨ 3,3⟩} | (x : ℝ) } := by sorry

theorem piecesMakeRotTiles : Piece = { {⟨(x:ℝ) ,(x : ℝ) ⟩} | x: (Fin 3)} := by sorry
