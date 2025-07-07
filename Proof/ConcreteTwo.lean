import Mathlib
import Proof.TileArea

#eval (canon_cor_rot Cor.tl [ Piece.treePiece 5 2 0])

#check Piece.treePiece


-- #eval (List.finRange 7).flatMap (fun i => List.map (fun j => Piece.treePiece i j 0)  (List.finRange 4))

namespace TestingTwo
def init : List Piece := (List.finRange 7).flatMap (fun i => List.map (fun j => Piece.treePiece i j 0)  (List.finRange 4))

def fn (xss : List (List Piece)) : List (List Piece) :=
  (List.mergeSort (xss ++ xss.flatMap
    (fun xs => List.map (fun r => canon_cor r xs)
                        [Cor.tl,Cor.br,Cor.bl,Cor.tr]))
     (· ≤ · )).dedup


partial def fn_fix (xss : List (List Piece)) : List (List Piece) :=
  let l := fn xss
  if l == xss then xss else (fn_fix l)


def plist : List (List Piece) := (fn_fix (List.map (· :: []) init))

#eval "plist2"
#eval (List.length plist)

partial def num_iters (xss : List (List Piece)) :  ℕ :=
  let l := fn xss
  if l == xss then (0:ℕ) else (1:ℕ) + (num_iters l)

#eval (num_iters (List.map (· :: []) init))


-- def plist2 : List (List Piece) := fn_fix  --  Nat.iterate fn 17 (List.map (· :: []) init)

-- #eval plist = fn plist

theorem plist_cont_all : plist = fn plist := by
  -- native_decide
  sorry

-- #eval (plist2.length) -- 4912?

end TestingTwo
-- def pl2

-- #eval (fn (List.map (· :: []) init))

-- #eval (fn_fix (List.map (· :: []) init))
-- #eval (fn_fix (List.map (· :: []) init))

-- #check (fn_fix init)

-- #eval (fn [init])
/-
def x3 := [
 [],
 [Piece.treePiece 0 0 3]]
def x2 := [
 [],
 [Piece.treePiece 0 0 3]]
-/
