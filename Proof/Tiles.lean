import Mathlib
import Proof.Pieces
import Proof.PythagTree
import Proof.Triangle
-- def Piece : Type := sorry

def pythagTree : Set (ℝ × ℝ) := sorry

def triangle : Set (ℝ × ℝ) := sorry

def grid := Fin 7 × Fin 4

def sqr (c : grid): Set R2 := square ⟨c.1-3,c.2⟩  1


-- def tile p := pythagTree ∩ (sqr p)
def gridPiece (c:grid) : Piece := treePiece c.1 c.2 Rot.none


-- def getCors (p: Piece) (c: Cor) : Set Piece :=
--   sorry


def getTile (p :Piece) : Set R2 := match p with
  | treePiece x y r => rotTransform r ''
      (AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨3-x, -y⟩ '' pythagTree) ∩ usq
  | trianglePiece r => rotTransform r '' triangle
  | fullPiece => usq
  | emptyPiece => ∅

lemma sq_add (dx dy : ℝ ):
  (fun x ↦ (dx, dy) + x) ⁻¹' square (dx,dy) 1 = square (0, 0) 1 := by
  ext ⟨x,y⟩
  simp [square]

def getTileIsInter (c : grid):
  getTile (gridPiece c) =
  AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨3-c.1, -c.2⟩ '' (pythagTree ∩ (sqr c)) := by
  simp only [getTile, gridPiece]
  simp [Rot.none,sqr,usq]
  rw [sq_add]

theorem getTileIsInter' (c : grid): getTile (gridPiece c) = pythagTree ∩ (sqr c) := by
  have x:pythagTree := by
    sorry
  obtain ⟨ ⟨a,b⟩,h⟩ := x
  sorry

-- def pieceMap (p : Piece) (cor : Cor) : List (Piece) := sorry

theorem pieceMap_makes_piece (p : Piece) (cor : Cor):
  getTile p ∩ (corTransform cor '' usq) = (corTransform cor '' Multiset.sup (List.map getTile (pieceMap p cor))) := by
  sorry
