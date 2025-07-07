import Mathlib
import Proof.TileArea

-- #eval (canon_cor_rot Cor.tl [ Piece.treePiece 5 2 0])

-- #check Piece.treePiece

-- #eval (List.finRange 7).flatMap (fun i => List.map (fun j => Piece.treePiece i j 0)  (List.finRange 4))


/-
partial def fn_fix (xss : List (List Piece)) : List (List Piece) :=
  let l := fn xss
  if l == xss then xss else (fn_fix l)


def plist : List (List Piece) := (fn_fix (List.map (· :: []) init))

#eval (List.length plist) -- 16

partial def num_iters (xss : List (List Piece)) :  ℕ :=
  let l := fn xss
  if l == xss then (0:ℕ) else (1:ℕ) + (num_iters l)

#eval (num_iters (List.map (· :: []) init)) --3785
-/

-- #eval plist = fn plist


def init : List (List Piece) := (List.finRange 7).flatMap (fun i => (List.finRange 4).map (fun j => [Piece.treePiece i j 0])  )

def all_pieces_needed_by (xss : List (List Piece)) : List (List Piece) :=
  (List.mergeSort (xss ++ xss.flatMap
    (fun xs => List.map (fun r => canon_cor_rot r xs)
                        [Cor.tl,Cor.br,Cor.bl,Cor.tr]))
     (· ≤ · )).dedup

def plist : List (List Piece) := Nat.iterate all_pieces_needed_by 17 (init)

theorem plist_cont_all : plist = all_pieces_needed_by plist := by
  -- decide -- After unfolding the instance 'instDecidableEqList', reduction got stuck at the 'Decidable' instance
            -- plist.hasDecEq (all_pieces_needed_by plist)
  native_decide

#eval (plist.length) -- 3785


-- #eval plist
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
