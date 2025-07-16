import Mathlib

import Proof.SquareDivision
import Proof.Pieces
import Proof.PythagTree

-- triangle stuff
def triangle : Set (ℝ×ℝ) := {⟨x,y⟩  | 0<x ∧ 0<y ∧  x+y<1}

def getTile (p :Piece) : Set R2 := match p with
  | .treePiece x y r => rotTransform r ''
      ((AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨-x, -y⟩ '' pythagTree) ∩ usq)
  | .trianglePiece r => rotTransform r '' triangle
  | .fullPiece => usq
  | .emptyPiece => ∅

def getTiles (ps : List Piece) : Set R2 := Multiset.sup (List.map getTile ps)

def canonical (l : List Piece) : List Piece:= (List.mergeSort l (· ≤ · )).dedup


def canon_cor (cor : Cor) (ps : List Piece) := canonical (List.flatMap (fun p => pieceMap p cor) ps)

def rotList (r :Rot) (ps : List Piece) : List Piece :=  List.map (rotatep r) ps

-- List.max?_mem
def canon_rot (ps : List Piece) : List Piece :=
  if .fullPiece ∈ ps ∨ (∃ k, .treePiece 3 0 k ∈ ps) then [.fullPiece] else
    Option.get (@List.max? _ (maxOfLe)  (List.map (fun r => canonical (rotList r ps)) [Rot.none, Rot.left, Rot.half, Rot.right]))
        (by
          simp only [List.map_cons, List.max?_cons', Option.isSome_some]
        )

def rem_empty (ps : List Piece) : List Piece :=
  if (List.getLast? ps) = some Piece.emptyPiece then List.dropLast ps else ps

def canon_cor_rot (cor : Cor) (ps : List Piece) := rem_empty (canon_rot (List.flatMap (fun p => pieceMap p cor) ps))

def init : List (List Piece) :=
  (List.finRange 7).flatMap
    (fun i => (List.finRange 4).map
      (fun j => [Piece.treePiece i j 0]))

noncomputable def vol := MeasureTheory.volume ∘ getTiles

noncomputable def vol' (ps: List Piece) : ℝ  := ENNReal.toReal (vol ps)
