import Mathlib
import Proof.SquareDivision
import Proof.Rotations

-- Is this a bad idea?
instance : Ord Rot where
  compare a b := compare a.val b.val

inductive Piece : Type
  | treePiece : Fin 7 → Fin 4 → Rot → Piece
  | trianglePiece : Rot → Piece -- (triangle none) is bottom left half of unit_sq
  | emptyPiece : Piece
  | fullPiece : Piece
  deriving DecidableEq,Ord,Repr

instance: LT Piece := ltOfOrd
instance: LE Piece := leOfOrd

open Piece
-- def pieces (s : Z2) (cor : Cor) : List (Piece) := sorry

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


-- TODO: carefully consider centering squares on integer coordinates

-- doubled position of bottom left of corner
def corPos (xn : Fin 7) (yn : Fin 4) (cor : Cor) : ℤ × ℤ  := match cor with
    | .bl => (2*xn,2*yn)
    | .tl => (2*xn,2*yn+1)
    | .tr => (2*xn+1,2*yn+1)
    | .br => (2*xn+1,2*yn)
-- Finset or list?
def treeMap (xn : Fin 7) (yn : Fin 4) (cor : Cor) : List Piece :=
  let ⟨px,py⟩  := (corPos xn yn cor)
  if xn=3 ∧ yn=0 then [fullPiece] else
  if yn=1 ∧ px>4 ∧ px < 9 then (match cor with
    | .bl => [trianglePiece Rot.right]
    | .tl => [trianglePiece Rot.none]
    | .tr => [trianglePiece Rot.left]
    | .br => [trianglePiece Rot.half]
  ) else List.flatMap (fun ⟨(⟨x,y⟩ : ℤ ×ℤ) ,r⟩ =>
     if 0≤x ∧ x<7 ∧ 0≤y ∧ y<4
        then [treePiece (Fin.ofNat 7 (Int.toNat x)) (Fin.ofNat 4 (Int.toNat y)) r]
        else []
    )
  [((py,4-px),Rot.left),
  ((px-2,py-4), Rot.none),((px-5,py-4), Rot.none),
  ((6-py,px-9),Rot.right)
  ]
-- In theory, I would like to have the same function transforming coordinates here as for transforming reals
-- (doesn't quite work because the bottom left corner when rotated isn't the bottom left corner overall)

def pieceMap (p : Piece) (cor : Cor) : List (Piece) := match p with
  | treePiece xn yn r => List.map (rotatep r) (treeMap xn yn (rotCor (- r) cor))
  | trianglePiece r => [rotatep r (triangleMap (rotCor (- r) cor))]
  | emptyPiece => []
  | fullPiece => [fullPiece]

#eval pieceMap (Piece.treePiece 2 2 Rot.none) Cor.tl

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
