import Mathlib
import Proof.SquareDivision
import Proof.Rotations

open SquareDiv

inductive Piece : Type
  | treePiece : Fin 7 → Fin 4 → Rot → Piece
  | trianglePiece : Rot → Piece -- (triangle none) is bottom left half of unit_sq
  | emptyPiece : Piece
  | fullPiece : Piece
open Piece
def pieces (s : Z2) (cor : Cor) : List (Piece) := sorry

def triangleMap (cor : Cor) : List Piece := sorry

def rotatep (r : Rot) (p:Piece) : Piece := match piece with
  | treePiece xn yn r => treePiece xn yn (rotCor r)
  | trianglePiece r => trianglePiece (rotCor r)
  | emptyPiece => emptyPiece
  | fullPiece => fullPiece

def pieceMap (p : Piece) (cor : Cor) : List (Piece) := match piece with
  | treePiece xn yn r => sorry
  | trianglePiece r => rotatep r (triangleMap rotCor)
  | emptyPiece => emptyPiece
  | fullPiece => fullPiece




-- def Piece : Type := sorry

def pythagTree : Set (ℝ × ℝ) := sorry

def grid := Fin 7 × Fin 4

def sqr (c : grid): Set R2 := square ⟨c.1,c.2⟩  1


-- def tile p := pythagTree ∩ (sqr p)
def tile (c:grid) : Piece := sorry
--#check SquareDiv.Piece
def getTile (p :Piece) : Set R2 := sorry -- (pieces could be Set R2)

def getCors (p: Piece) (c: Cor) : Set Piece :=
  sorry


def getTileIsInter (c : grid):
  getTile (tile c) =
  AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨3-c.1, -c.2⟩ '' (pythagTree ∩ (sqr c)) := by
  sorry

theorem getTileIsInter' (c : grid): getTile (tile c) = pythagTree ∩ (sqr c) := by
  have x:pythagTree := by
    sorry
  obtain ⟨ ⟨a,b⟩,h⟩ := x
  sorry

def pieceMap (p : Piece) (cor : Cor) : List (Piece) := sorry

theorem pieceMap_makes_piece (p : Piece) (cor : Cor):
  getTile p ∩ (corTransform cor '' usq) = (corTransform cor '' Multiset.sup (List.map getTile (pieceMap p cor))) := by
  sorry
