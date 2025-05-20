import Mathlib
import Proof.SquareDivision
import Proof.Pieces
import Proof.PythagTree
-- def Piece : Type := sorry

-- def pythagTree : Set (ℝ × ℝ) := sorry
def triangle : Set (ℝ×ℝ) := {⟨x,y⟩  | 0<x ∧ 0<y ∧  x+y<1}

def getTile (p :Piece) : Set R2 := match p with
  | .treePiece x y r => rotTransform r ''
      (AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨-x, -y⟩ '' pythagTree) ∩ usq
  | .trianglePiece r => rotTransform r '' triangle
  | .fullPiece => usq
  | .emptyPiece => ∅

-- triangle stuff

lemma tri_in_sq : triangle ⊆ usq := by
  unfold triangle usq square
  intro ⟨ x,y⟩
  simp
  bound

theorem triMap_makes_tri (cor : Cor): triangle ∩ (corTransform cor '' usq) = (corTransform cor '' getTile (triangleMap cor)) := by
  have h1 {a b:ℝ }:2⁻¹ * a = b ↔ a = 2*b := by norm_num; bound
  have h2 {a b:ℝ }:2⁻¹ * a + 2⁻¹ = b ↔ a = 2*b - 1 := by norm_num; bound
  rcases cor <;> (
    simp only [triangleMap,getTile,rotTransform,Rot.none,AffineEquiv.refl_apply, Set.image_id']
    unfold usq
    rw [sq_cors]
    ext ⟨ x,y⟩
    simp only [corTransform]
    unfold triangle square
    simp [h1,h2]
    norm_num
    (try apply Iff.intro) <;>(
      intros
      and_intros <;> linarith
    )
  )






def grid := Fin 7 × Fin 4

def sqr (c : grid): Set R2 := square ⟨c.1,c.2⟩  1


-- def tile p := pythagTree ∩ (sqr p)
def gridPiece (c:grid) : Piece := .treePiece c.1 c.2 Rot.none


-- def getCors (p: Piece) (c: Cor) : Set Piece :=
--   sorry




lemma sq_add (dx dy : ℝ ):
  (fun x ↦ (dx, dy) + x) ⁻¹' square (dx,dy) 1 = square (0, 0) 1 := by
  ext ⟨x,y⟩
  simp [square]

def getTileIsInter (c : grid):
  getTile (gridPiece c) =
  AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨-c.1, -c.2⟩ '' (pythagTree ∩ (sqr c)) := by
  simp only [getTile, gridPiece]
  simp [Rot.none,sqr,usq]
  rw [sq_add]

/- An alternative definition of getTile would have the following property
theorem getTileIsInter' (c : grid): getTile (gridPiece c) = pythagTree ∩ (sqr c) := by
  have x:pythagTree := by
    sorry
  obtain ⟨ ⟨a,b⟩,h⟩ := x
  sorry
-/
-- def pieceMap (p : Piece) (cor : Cor) : List (Piece) := sorry
lemma cor_sq_ss (cor : Cor) : (corTransform cor) '' usq ⊆ usq := by
  cases' cor <;>(
    simp [corTransform,usq,square]
    intro ⟨x,y⟩
    simp
    norm_num
    bound
  )
open Set

@[simp] theorem val_three {n : Nat} : (3 : Fin (n + 4)).val = 3 := rfl

theorem treeMap_makes_piece (cx : Fin 7) (cy : Fin 4) (cor : Cor):
  (corTransform cor '' usq) ∩ (getTile (.treePiece cx cy Rot.none)) =
   (corTransform cor '' Multiset.sup (List.map getTile (treeMap cx cy cor))) := by
  rw [getTile]
  unfold Rot.none
  rw [rotTransform]
  rw [AffineEquiv.coe_refl,Set.image_id]
  rw [Set.inter_comm]
  rw [Set.inter_assoc]
  -- #check (Set.le_iff_subset.mpr (cor_sq_ss cor))
  -- #check min_eq_right (cor_sq_ss cor)
  rw [Set.inter_eq_self_of_subset_right (cor_sq_ss cor)]
  -- ext ⟨x,y⟩
  unfold treeMap
  by_cases h : (cx=3 ∧ cy=0)
  . simp only [if_pos h]
    rw [h.left,h.right]
    simp_all only [Fin.isValue, Fin.val_zero, CharP.cast_eq_zero, neg_zero, AffineEquiv.constVAdd_apply, vadd_eq_add,
       Prod.neg_mk, neg_neg,  Prod.mk_add_mk, zero_add,
       List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.sup_singleton,getTile]
    rw [Set.inter_eq_right]
    apply subset_trans (cor_sq_ss cor)
    apply (subset_trans _ (Set.monotone_image sq_ss_pyt))
    simp [usq,square]
    intro ⟨x,y⟩
    simp
    bound
  . simp only [if_neg h]
    sorry


theorem pieceMap_makes_piece (p : Piece) (cor : Cor):
  getTile p ∩ (corTransform cor '' usq) = (corTransform cor '' Multiset.sup (List.map getTile (pieceMap p cor))) := by
  sorry
