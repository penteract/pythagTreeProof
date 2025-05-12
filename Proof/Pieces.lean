import Mathlib
import Proof.SquareDivision
import Proof.Rotations

open SquareDiv

inductive Piece : Type
  | treePiece : Fin 7 → Fin 4 → Rot → Piece
  | trianglePiece : Rot → Piece -- (triangle none) is bottom left half of unit_sq
  | emptyPiece : Piece
  | fullPiece : Piece
  deriving DecidableEq
open Piece
def pieces (s : Z2) (cor : Cor) : List (Piece) := sorry

def triangleMap (cor : Cor) : Piece := match cor with
  | .bl => fullPiece
  | .tr => emptyPiece
  | _ => trianglePiece Rot.none

def rotatep (r : Rot) (piece:Piece) : Piece := match piece with
  | treePiece xn yn r' => treePiece xn yn (r + r')
  | trianglePiece r' => trianglePiece (r + r')
  | emptyPiece => emptyPiece
  | fullPiece => fullPiece

theorem rotatep_hom(r : Rot) (r' : Rot) : rotatep (r + r') = rotatep r ∘ (rotatep r') := by
  ext p
  simp
  cases p
  simp only [rotatep,add_assoc]
  simp only [rotatep,add_assoc]
  simp only [rotatep]
  simp only [rotatep]

-- Finset or list?
def treeMap (xn : Fin 7) (yn : Fin 4) (cor : Cor) : List Piece := sorry

def pieceMap (p : Piece) (cor : Cor) : List (Piece) := match p with
  | treePiece xn yn r => List.map (rotatep r) (treeMap xn yn (rotCor (- r) cor))
  | trianglePiece r => [rotatep r (triangleMap (rotCor (- r) cor))]
  | emptyPiece => []
  | fullPiece => [fullPiece]

theorem pieceMap_rot_comm (p : Piece) (r : Rot) (cor:Cor) :
  pieceMap (rotatep r p) (rotCor r cor) = List.map (rotatep r) (pieceMap p cor) := by
  rcases p  with ⟨ x,y,rr ⟩|rr|⟨⟩|⟨⟩
  . simp only [pieceMap,rotatep]
    rw [rotatep_hom]
    rw [← @Function.comp_apply  _ _ _ (rotCor (-(r + rr))) ]
    rw [← rotCor_hom]
    simp
  . simp only [rotatep]
    simp only [pieceMap,List.map]
    rw [rotatep_hom]
    rw [← @Function.comp_apply  _ _ _ (rotCor (-(r + rr))) ]
    rw [← rotCor_hom]
    simp
  . simp only [pieceMap,rotatep,List.map]
  . simp only [pieceMap,rotatep,List.map]

def multiPieceMap (ps : List Piece) (cor : Cor) : List Piece :=
  List.eraseDups (List.flatMap (fun p => pieceMap p cor) ps)


-- def Piece : Type := sorry

def pythagTree : Set (ℝ × ℝ) := sorry

def grid := Fin 7 × Fin 4

def sqr (c : grid): Set R2 := square ⟨c.1,c.2⟩  1


-- def tile p := pythagTree ∩ (sqr p)
def gridPiece (c:grid) : Piece := sorry


def getCors (p: Piece) (c: Cor) : Set Piece :=
  sorry


def getTile (p :Piece) : Set R2 := sorry

def getTileIsInter (c : grid):
  getTile (gridPiece c) =
  AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨3-c.1, -c.2⟩ '' (pythagTree ∩ (sqr c)) := by
  sorry

theorem getTileIsInter' (c : grid): getTile (gridPiece c) = pythagTree ∩ (sqr c) := by
  have x:pythagTree := by
    sorry
  obtain ⟨ ⟨a,b⟩,h⟩ := x
  sorry

-- def pieceMap (p : Piece) (cor : Cor) : List (Piece) := sorry

theorem pieceMap_makes_piece (p : Piece) (cor : Cor):
  getTile p ∩ (corTransform cor '' usq) = (corTransform cor '' Multiset.sup (List.map getTile (pieceMap p cor))) := by
  sorry
