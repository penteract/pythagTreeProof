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

lemma lem : f = fun x => f x := by
  simp_all only

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

lemma union_mess {a b c d e f g : Set (ℝ×ℝ)} :
 a ∪
    (b ∪
      (c ∪
        (d ∪
          (e ∪ (f ∪ g))))) =
  g ∪
    (f ∪
      (d ∪
        (c ∪ (e
          ∪ (a ∪ b)))))
        := by
        aesop

theorem pyt_is_union : pythagTree = Ioo 3 4 ×ˢ Ioo 0 1
  ∪ d0 '' (Ioo 3 4 ×ˢ Ioo 0 1) ∪ d1 '' (Ioo 3 4 ×ˢ Ioo 0 1)
  ∪ d0 '' (d0 '' pythagTree) ∪ d0 '' (d1 '' pythagTree)
  ∪ d1 '' (d0 '' pythagTree) ∪ d1 '' (d1 '' pythagTree) := by
  calc pythagTree
    _ = OrderHom.lfp treeFun_m := by
      unfold pythagTree
      rfl
    _ = treeFun_m (treeFun_m (OrderHom.lfp treeFun_m)) := by
      nth_rw 1 [← OrderHom.map_lfp]
      nth_rw 1 [← OrderHom.map_lfp]
    _ = treeFun_m (treeFun_m pythagTree) := by
      rw [← pythagTree]
    --_ = OrderHom.lfp (treeFun_m.comp treeFun_m) := (lfp_f_eq_lfp_ff _)
    _ = _ := by
      simp only [treeFun_m,OrderHom.coe_mk,treeFun]
      simp only [Set.image_union]
      --simp only [Set.union_assoc, Set.union_comm]
      simp [-d0, -d1, Set.union_assoc, ← Set.union_comm]
      exact union_mess

      -- aesop?

theorem d00_pyt_in_rect : d0 '' (d0 '' pythagTree) ⊆ Ioo 0.5 2.5 ×ˢ Ioo 0 3.5 := by
  intro ⟨x,y⟩
  rw [← Set.image_comp]
  intro h
  rw [mem_image] at h
  obtain ⟨⟨ w,z⟩ ,⟨ h1,h2⟩ ⟩ := h
  rw [Function.comp_apply,d00] at h2
  rw [← h2]
  have hh := mem_of_mem_of_subset h1 pyt_in_rect
  unfold pythag_rect at hh
  simp at *
  bound

theorem d01_pyt_in_rect : d0 '' (d1 '' pythagTree) ⊆ Ioo 1 4.5 ×ˢ Ioo 2 4 := by
  intro ⟨x,y⟩
  rw [← Set.image_comp]
  intro h
  rw [mem_image] at h
  obtain ⟨⟨ w,z⟩ ,⟨ h1,h2⟩ ⟩ := h
  rw [Function.comp_apply,d01] at h2
  rw [← h2]
  have hh := mem_of_mem_of_subset h1 pyt_in_rect
  unfold pythag_rect at hh
  simp at *
  rw [right_distrib] -- not sure why I need this
  bound

theorem d10_pyt_in_rect : d1 '' (d0 '' pythagTree) ⊆ Ioo 2.5 6 ×ˢ Ioo 2 4 := by
  intro ⟨x,y⟩
  rw [← Set.image_comp]
  intro h
  rw [mem_image] at h
  obtain ⟨⟨ w,z⟩ ,⟨ h1,h2⟩ ⟩ := h
  rw [Function.comp_apply,d10] at h2
  rw [← h2]
  have hh := mem_of_mem_of_subset h1 pyt_in_rect
  unfold pythag_rect at hh
  simp at *
  bound

theorem d11_pyt_in_rect : d1 '' (d1 '' pythagTree) ⊆ Ioo 4.5 6.5 ×ˢ Ioo 0 3.5 := by
  intro ⟨x,y⟩
  rw [← Set.image_comp]
  intro h
  rw [mem_image] at h
  obtain ⟨⟨ w,z⟩ ,⟨ h1,h2⟩ ⟩ := h
  rw [Function.comp_apply,d11] at h2
  rw [← h2]
  have hh := mem_of_mem_of_subset h1 pyt_in_rect
  unfold pythag_rect at hh
  simp at *
  bound
theorem d0_sq_in_rect : d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ⊆ Ioo 2.5 3.5 ×ˢ Ioo 1 2 := by
  intro ⟨ x,y⟩
  intro h
  replace ⟨⟨w,z⟩ ,⟨ h,hh⟩ ⟩  := h
  rw [← hh]
  simp at *
  norm_num at *
  rw [sub_mul]
  bound
theorem d1_sq_in_rect : d1 '' Ioo 3 4 ×ˢ Ioo 0 1 ⊆ Ioo 3.5 4.5 ×ˢ Ioo 1 2 := by
  intro ⟨ x,y⟩
  intro h
  replace ⟨⟨w,z⟩ ,⟨ h,hh⟩ ⟩  := h
  rw [← hh]
  simp at *
  norm_num at *
  and_intros
  bound
  bound
  rw [add_mul]
  bound
  bound

theorem pythag_sq1 : pythagTree ∩ Ioo 2.5 3.5 ×ˢ Ioo 1 2 = d0 '' (Ioo 3 4 ×ˢ Ioo 0 1) := by
  rw [pyt_is_union]
  simp only [Set.union_inter_distrib_right]
  conv_lhs =>
    congr
    congr
    congr
    congr
    congr
    arg 1
    all_goals (rw [Disjoint.inter_eq]; rfl)
    tactic =>
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d1_sq_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d00_pyt_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d01_pyt_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d10_pyt_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d11_pyt_in_rect
      bound
  repeat (rw [union_empty])
  rw [empty_union]
  exact (Set.inter_eq_self_of_subset_left d0_sq_in_rect)

theorem pythag_sq2 : pythagTree ∩ Ioo 3.5 4.5 ×ˢ Ioo 1 2 = d1 '' (Ioo 3 4 ×ˢ Ioo 0 1) := by
  rw [pyt_is_union]
  simp only [Set.union_inter_distrib_right]
  conv_lhs =>
    congr
    congr
    congr
    congr
    arg 1
    congr
    all_goals (rw [Disjoint.inter_eq]; rfl)
    tactic =>
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d0_sq_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d00_pyt_in_rect
      bound
    tactic =>
      apply Set.disjoint_of_subset_left d01_pyt_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d10_pyt_in_rect
      simp
    tactic =>
      apply Set.disjoint_of_subset_left d11_pyt_in_rect
      simp
  repeat (rw [union_empty])
  rw [empty_union]
  exact (Set.inter_eq_self_of_subset_left d1_sq_in_rect)

theorem tri_half : (⇑(rotTransform Rot.half) '' triangle) = {⟨x,y⟩  | (x<1)  ∧ (y<1) ∧  x+y>1} := by
  unfold rotTransform Rot.half triangle
  ext ⟨ x,y⟩
  simp
  unfold AffineMap.homothety
  simp
  have h (a:ℝ) : (2⁻¹ - a + 2⁻¹ = x) ↔ (a = 1-x) := by
    norm_num
    bound
  have h' (b:ℝ) : 2⁻¹ - b + 2⁻¹ = y ↔ b=1-y := by
    norm_num
    bound
  simp [h,h']
  bound
theorem tri_left : (⇑(rotTransform Rot.left) '' triangle) = {⟨x,y⟩  | (x<1)  ∧ (0<y) ∧  y<x} := by
  unfold rotTransform Rot.left triangle
  simp
  ext ⟨ x,y⟩
  simp [AffineIsometryEquiv.constVAdd,rotLeft, AffineIsometryEquiv.symm]
  have h (a:ℝ) : 2⁻¹ + (-a + 2⁻¹) = x ↔ (a = 1-x) := by
    norm_num
    bound
  simp [h]
  bound
theorem tri_right : (⇑(rotTransform Rot.right) '' triangle) = {⟨x,y⟩  | (y<1)  ∧ (0<x) ∧  x<y} := by
  unfold rotTransform Rot.right triangle
  simp
  ext ⟨ x,y⟩
  simp [AffineIsometryEquiv.constVAdd,rotLeft, AffineIsometryEquiv.symm]
  have h (a:ℝ) : 2⁻¹ + (-a + 2⁻¹) = y ↔ (a = 1-y) := by
    norm_num
    bound
  simp [h]
  bound


theorem sq_is_rot_tri_1 : (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-2, -1)) ''
    (d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 2.5 3 ×ˢ Ioo 1 (3 / 2)) =
    (fun a ↦ (2:ℝ)⁻¹ • a + (2⁻¹, 0)) '' (⇑(rotTransform «Rot».half) '' triangle) := by
  -- ext ⟨ x,y⟩
  rw [tri_half]
  simp
  ext ⟨x,y⟩
  simp
  have h (a b : ℝ) : (a - b + 3) * 0.5 = 2 + x ∧ (a + b - 1) * 0.5 = 1 + y
    ↔ a = (x+y) + 2 ∧ b = y - x + 1
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a + 2⁻¹ = x ∧ 2⁻¹ * b = y ↔ a = 2*x - 1 ∧ b = 2*y := by
    bound
  simp [h,h']
  norm_num
  bound

lemma l1 {x : ℝ } : 5 / 2 < 2 + x → 1<2*x := by
  intro h
  linarith
  /-
  replace h:= add_lt_add_right h (-4/2)
  norm_num at h
  rw [← (mul_lt_mul_left (by bound : 0<(2:ℝ) ))] at h
  simp at h
  exact h-/
theorem sq_is_rot_tri_2 : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-2, -1)) a) ''
    (d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 2.5 3 ×ˢ Ioo (3 / 2) 2) =
  (fun a ↦ (2:ℝ)⁻¹ • a + (2⁻¹, 2⁻¹)) '' (⇑(rotTransform «Rot».left) '' triangle) := by

  rw [tri_left]
  simp
  ext ⟨x,y⟩
  simp
  have h (a b : ℝ) : (a - b + 3) * 0.5 = 2 + x ∧ (a + b - 1) * 0.5 = 1 + y
    ↔ a = (x+y) + 2 ∧ b = y - x + 1
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a + 2⁻¹ = x ∧ 2⁻¹ * b + 2⁻¹ = y ↔ a = 2*x - 1 ∧ b = 2*y - 1 := by
    bound
  simp [h,h']
  norm_num at *
  apply Iff.intro
  . intro h
    apply And.intro
    bound
    apply And.intro
    linarith -- don't ask me why bound doesn't solve this one (see l1)
    bound
  . bound

theorem sq_is_rot_tri_3 :(fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-3, -1)) a) '' (d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 3 3.5 ×ˢ Ioo 1 (3 / 2)) =
  (fun a ↦ (2:ℝ)⁻¹ • a) '' (⇑(rotTransform «Rot».right) '' triangle) := by
  rw [tri_right]
  simp
  ext ⟨ x,y⟩
  simp
  have h (a b : ℝ) : (a - b + 3) * 0.5 = 3 + x ∧ (a + b - 1) * 0.5 = 1 + y
    ↔ a = (x+y) + 3 ∧ b = y - x + 0
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a = x ∧ 2⁻¹ * b = y ↔ a = 2*x ∧ b = 2*y := by
    bound
  simp [h,h']
  bound

theorem sq_is_rot_tri_4 : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-3, -1)) a) '' (d1 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 3.5 4 ×ˢ Ioo 1 (3 / 2)) =
  (fun a ↦ (2:ℝ)⁻¹ • a + (2⁻¹, 0)) '' (⇑(rotTransform «Rot».half) '' triangle) := by
  rw [tri_half]
  simp
  ext ⟨ x,y⟩
  simp
  have h (a b : ℝ) : (a + b + 4) * 0.5 = 3 + x ∧ (b - a + 6) * 0.5 = 1 + y
    ↔ a = (x-y) + 3 ∧ b = y + x - 1
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a + 2⁻¹ = x ∧ 2⁻¹ * b = y ↔ a = 2*x - 1 ∧ b = 2*y := by
    bound
  simp [h,h']
  bound

theorem sq_is_rot_tri_5 : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-3, -1)) a) '' (d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 3 3.5 ×ˢ Ioo (3 / 2) 2) =
  (fun a ↦ (2:ℝ)⁻¹ • a + (0, 2⁻¹)) '' (⇑(rotTransform «Rot».none) '' triangle):= by
  simp [Rot.none]
  unfold triangle
  ext ⟨ x,y⟩
  simp
  have h (a b : ℝ) : (a - b + 3) * 0.5 = 3 + x ∧ (a + b - 1) * 0.5 = 1 + y
    ↔ a = (x+y) + 3 ∧ b = y - x + 0
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a  = x ∧ 2⁻¹ * b+ 2⁻¹ = y ↔ a = 2*x ∧ b = 2*y - 1 := by
    bound
  simp [h,h']
  apply Iff.intro
  intro h
  and_intros
  bound
  linarith -- again
  bound
  bound

theorem sq_is_rot_tri_6 : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-3, -1)) a) '' (d1 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 3.5 4 ×ˢ Ioo (3 / 2) 2) =
  (fun a ↦ (2:ℝ)⁻¹ • a + (2⁻¹, 2⁻¹)) '' (⇑(rotTransform «Rot».left) '' triangle) := by
  rw [tri_left]
  simp
  ext ⟨x,y⟩
  simp
  have h (a b : ℝ) : (a + b + 4) * 0.5 = 3 + x ∧ (b - a + 6) * 0.5 = 1 + y
    ↔ a = (x-y) + 3 ∧ b = y + x - 1
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a + 2⁻¹ = x ∧ 2⁻¹ * b + 2⁻¹ = y ↔ a = 2*x - 1 ∧ b = 2*y - 1 := by
    bound
  simp [h,h']
  norm_num at *
  apply Iff.intro
  . intro h
    apply And.intro
    bound
    apply And.intro
    linarith -- again
    bound
  . bound

theorem sq_is_rot_tri_7 : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-4, -1)) a) '' (d1 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 4 4.5 ×ˢ Ioo 1 (3 / 2)) =
  (fun a ↦ (2:ℝ)⁻¹ • a) '' (⇑(rotTransform «Rot».right) '' triangle) := by
  rw [tri_right]
  simp
  ext ⟨ x,y⟩
  simp
  have h (a b : ℝ) :(a + b + 4) * 0.5 = 4 + x ∧ (b - a + 6) * 0.5 = 1 + y
    ↔ a = (x-y) + 4 ∧ b = y + x
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a = x ∧ 2⁻¹ * b = y ↔ a = 2*x ∧ b = 2*y := by
    bound
  simp [h,h']
  bound

theorem sq_is_rot_tri_8 : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-4, -1)) a) '' (d1 '' Ioo 3 4 ×ˢ Ioo 0 1 ∩ Ioo 4 4.5 ×ˢ Ioo (3 / 2) 2) =
  (fun a ↦ (2:ℝ)⁻¹ • a + (0, 2⁻¹)) '' (⇑(rotTransform «Rot».none) '' triangle) := by
  simp [Rot.none]
  unfold triangle
  ext ⟨ x,y⟩
  simp
  have h (a b : ℝ) :(a + b + 4) * 0.5 = 4 + x ∧ (b - a + 6) * 0.5 = 1 + y
    ↔ a = (x-y) + 4 ∧ b = y + x
  := by
    bound
  have h' (a b : ℝ ) : 2⁻¹ * a  = x ∧ 2⁻¹ * b+ 2⁻¹ = y ↔ a = 2*x ∧ b = 2*y - 1 := by
    bound
  simp [h,h']
  apply Iff.intro
  intro h
  and_intros
  bound
  linarith -- again
  bound
  bound


theorem image_intervals {s : Set (ℝ × ℝ)}
  : (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) p) a) '' s ∩ Ioo a b ×ˢ Ioo c d
     = (fun a ↦ (AffineEquiv.constVAdd ℝ (ℝ × ℝ) p) a) '' (s ∩ Ioo (a-p.1) (b-p.1) ×ˢ Ioo (c-p.2) (d-p.2))
  := by
  simp
  apply congrArg _
  obtain ⟨fst, snd⟩ := p
  simp_all only [Prod.neg_mk]
  ext x
  simp_all only [mem_prod, mem_Ioo, mem_preimage, Prod.fst_add, lt_neg_add_iff_add_lt, add_sub_cancel,
    neg_add_lt_iff_lt_add, Prod.snd_add]
theorem image_intervals' {s : Set (ℝ × ℝ)}
  :  (AffineEquiv.constVAdd ℝ (ℝ × ℝ) p) '' s ∩ Ioo a b ×ˢ Ioo c d
     = (AffineEquiv.constVAdd ℝ (ℝ × ℝ) p) '' (s ∩ Ioo (a-p.1) (b-p.1) ×ˢ Ioo (c-p.2) (d-p.2))
  := by
  simp
  apply congrArg _
  obtain ⟨fst, snd⟩ := p
  simp_all only [Prod.neg_mk]
  ext x
  simp_all only [mem_prod, mem_Ioo, mem_preimage, Prod.fst_add, lt_neg_add_iff_add_lt, add_sub_cancel,
    neg_add_lt_iff_lt_add, Prod.snd_add]

theorem second_gen_squares
  (cx : Fin 7)
  (cy : Fin 4)
  (cor : Cor)
  (h : ¬(cx = 3 ∧ cy = 0))
  : cy = 1 ∧ (corPos cx cy cor).1 > 4 ∧ (corPos cx cy cor).1 < 9 → -- Naming this argument breaks things
   ⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑↑cx, -↑↑cy)) '' pythagTree ∩ ⇑(corTransform cor) '' usq =
      ⇑(corTransform cor) ''
        Multiset.sup (List.map getTile
            (match cor with
              | Cor.bl => [Piece.trianglePiece «Rot».right]
              | Cor.tl => [Piece.trianglePiece «Rot».none]
              | Cor.tr => [Piece.trianglePiece «Rot».left]
              | Cor.br => [Piece.trianglePiece «Rot».half])) := by
  intro h'
  fin_cases cy <;> simp at h'
  (fin_cases cx <;> fin_cases cor <;> simp [corPos] at h') <;> (
    simp [-AffineEquiv.constVAdd_apply]
    unfold usq
    rw [sq_cors]
    unfold square
    simp [corTransform,-AffineEquiv.constVAdd_apply]
    rw [image_intervals]
  )
  . have sq_s : Ioo ((5:ℝ) / 2) (3:ℝ) ×ˢ Ioo (1:ℝ) ((3:ℝ) / 2) ⊆ Ioo (5/2) (7/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 5/2 = (2.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq1]
    simp only [getTile]
    rw [sq_is_rot_tri_1]
  . have sq_s : Ioo ((5:ℝ) / 2) (3:ℝ) ×ˢ Ioo  ((3:ℝ) / 2) (2:ℝ) ⊆ Ioo (5/2) (7/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 5/2 = (2.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq1]
    simp only [getTile]
    rw [sq_is_rot_tri_2]
  . have sq_s : Ioo (3:ℝ ) ((7:ℝ) /2) ×ˢ Ioo  (1:ℝ)  ((3:ℝ) / 2) ⊆ Ioo (5/2) (7/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 5/2 = (2.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq1]
    simp only [getTile]
    rw [sq_is_rot_tri_3]
  . have sq_s : Ioo ((7:ℝ) /2) (4:ℝ ) ×ˢ Ioo  (1:ℝ)  ((3:ℝ) / 2) ⊆ Ioo (7/2) (9/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 9/2 = (4.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq2]
    simp only [getTile]
    rw [sq_is_rot_tri_4]
  . have sq_s : Ioo (3:ℝ ) ((7:ℝ) /2) ×ˢ Ioo  (3 / 2) 2 ⊆ Ioo (5/2) (7/2) ×ˢ Ioo (1:ℝ) (2:ℝ) := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 5/2 = (2.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq1]
    simp only [getTile]
    rw [sq_is_rot_tri_5]
  . have sq_s : Ioo ((7:ℝ) /2) (4:ℝ )  ×ˢ Ioo ((3:ℝ) / 2) (2:ℝ) ⊆ Ioo (7/2) (9/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 9/2 = (4.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq2]
    simp only [getTile]
    rw [sq_is_rot_tri_6]
  . have sq_s : Ioo (4:ℝ) ((9:ℝ) /2)  ×ˢ Ioo (1:ℝ) ((3:ℝ) / 2) ⊆ Ioo (7/2) (9/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 9/2 = (4.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq2]
    simp only [getTile]
    rw [sq_is_rot_tri_7]
  . have sq_s : Ioo (4:ℝ) ((9:ℝ) /2)  ×ˢ Ioo ((3:ℝ) / 2) (2:ℝ) ⊆ Ioo (7/2) (9/2) ×ˢ Ioo 1 2 := by
      apply Set.prod_subset_prod_iff.mpr
      apply Or.intro_left
      rw [Set.subset_def, Set.subset_def]
      simp
      bound
    conv_lhs =>
      arg 2
      norm_num
      rw [← (Set.inter_eq_self_of_subset_left sq_s)]
      conv =>
        rhs
        rw [inter_comm]
      rw [← inter_assoc]
      rw [ (by norm_num : 9/2 = (4.5:ℝ))]
      rw [ (by norm_num : 7/2 = (3.5:ℝ))]
      rw [pythag_sq2]
    simp only [getTile]
    rw [sq_is_rot_tri_8]

lemma preimage_inter_inter_image {α β : Type } (t : Set β) (s u: Set α) (f : α → β) :
  f ⁻¹' t ∩ u = s → t ∩ f '' u = f '' s := by
    intro h
    apply congrArg (fun x => f '' x) at h
    rw [Set.image_preimage_inter] at h
    trivial

lemma inter_preimage_image_inter {α β : Type } (t : Set β) (s u: Set α) (f : α → β) :
  u ∩ f ⁻¹' t  = s → f '' u ∩ t = f '' s := by
    intro h
    apply congrArg (fun x => f '' x) at h
    rw [Set.image_inter_preimage] at h
    trivial

theorem image_inter_switch {α β : Type } (t : Set β) (s u: Set α) (f : α ≃ β) :
    t ∩ f '' u = f '' s ↔ f ⁻¹' t ∩ u = s := by
  constructor
  . rw [Set.preimage_equiv_eq_image_symm]
    rw [Set.image_equiv_eq_preimage_symm]
    rw [Set.image_equiv_eq_preimage_symm]
    intro h
    apply congrArg (fun x => f.symm '' x) at h
    rw [Set.image_inter_preimage] at h
    simp at h
    trivial
  . exact preimage_inter_inter_image t s u f
    /- intro h
    apply congrArg (fun x => f '' x) at h
    rw [Set.image_preimage_inter] at h
    trivial -/
/--/
lemma preimage_inter_inter_image' {α β : Type } (t t' : Set β) (u u': Set α) (f : α → β) :
  f ⁻¹' t ∩ u = f ⁻¹' t' ∩ u' → t ∩ f '' u = t' ∩ f '' u' := by
  intro h
  apply preimage_inter_inter_image at h
  rw [Set.image_preimage_inter] at h
  trivial-/
/-
lemma preimage_inter_inter_image' {α β : Type } (t t' : Set β) (u u': Set α) (f : β → α) :
  t ∩ f ⁻¹' u = t' ∩ f ⁻¹' u' → f '' t ∩ u = f '' t' ∩ u' := by
  intro h
  rw [inter_comm] at h
  nth_rw 2 [inter_comm] at h
  apply preimage_inter_inter_image at h
  rw [Set.image_preimage_inter] at h
  simp [inter_comm]
  exact h
-/
theorem AEq (e : (ℝ×ℝ) ≃ᵃ[ℝ ] ℝ×ℝ) : AffineEquiv.toEquiv e = EquivLike.toEquiv e := by
  rfl
theorem AffineEquiv.coe_toEquiv_symm (e : (ℝ×ℝ) ≃ᵃ[ℝ ] ℝ×ℝ) : e.toEquiv.symm = ↑e.symm := by
  simp_all only [symm_toEquiv]
  rfl

-- t = pythagtree
theorem simp_subsq_pyt
  (hh: (p1,p2) = corPos cx cy cor):
  ⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑↑cx, -↑↑cy)) '' t ∩ ⇑(corTransform cor) '' usq =
    ⇑(corTransform cor) '' s ↔
  ((AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-p1, -p2)) '' ((fun x => (2:ℝ) • x) '' t)) ∩ usq = s := by
  rw [corTransform_same]
  rw [← (EquivLike.coe_coe (corTransform' cor))]
  rw [image_inter_switch]
  apply Eq.congr_left
  apply (congrArg (fun x => x ∩ usq))
  rw [Set.preimage_equiv_eq_image_symm]
  rw [← Set.image_comp]
  rw [← Set.image_comp]
  apply congrFun
  apply congrArg
  fin_cases cor <;>(
    rw [← AEq]
    rw [AffineEquiv.symm_toEquiv]
    unfold corTransform'
    unfold corPos at hh
    simp at *
    ext ⟨x,y⟩ <;>(
      simp
      rw [AffineMap.homothety_apply]
      simp
      simp_all only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast, Int.cast_one, neg_add_rev]
      obtain ⟨left, right⟩ := hh
      subst right left
      linarith
    )
  )

lemma union_inter_left_empty {a b c : Set α} : a ∩ b = ∅ → (a ∪ c) ∩ b = c ∩ b := by
  intro h
  rw [union_inter_distrib_right]
  rw [h,empty_union]

set_option maxHeartbeats 1000000
lemma l2 {x y : ℝ}  {cx cy cor}
  (h : ¬(cx = 3 ∧ cy = 0))
  (h' : ¬(cy = 1 ∧ (corPos cx cy cor).1 > 4 ∧ (corPos cx cy cor).1 < 9)) :
  ((3 < x ∧ x < 4) ∧ 0 < y ∧ y < 1 ∨ (3 < x + y - 1 ∧ x + y - 1 < 4) ∧ 0 < y - x + 2 ∧ y - x + 2 < 1) ∨
    (3 < x - y + 1 ∧ x - y + 1 < 4) ∧ 5 < x + y ∧ x + y - 5 < 1 →
  ↑(corPos cx cy cor).1 < 2 * x →
    2 * x < ↑(corPos cx cy cor).1 + 1 → ↑(corPos cx cy cor).2 < 2 * y → ↑(corPos cx cy cor).2 + 1 ≤ 2 * y := by
    fin_cases cy
    . (fin_cases cx <;> try simp at h) <;>
       fin_cases cor <;> (
        simp [corPos]
        bound)
    . (fin_cases cx <;> fin_cases cor <;>
        simp [corPos] at h') <;> (
        simp [corPos]
        bound)
    . fin_cases cor <;> (
      simp [corPos]
      bound)
    . fin_cases cor <;> (
      simp [corPos]
      bound)

set_option maxHeartbeats 200000

theorem pyt_notbase_inter_base_empty
  (h : ¬(cx = 3 ∧ cy = 0))
  (h' : ¬(cy = 1 ∧ (corPos cx cy cor).1 > 4 ∧ (corPos cx cy cor).1 < 9))
  : (Ioo 3 4 ×ˢ Ioo 0 1 ∪ d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ∪ d1 '' Ioo 3 4 ×ˢ Ioo 0 1) ∩
    (⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑(corPos cx cy cor).1, -↑(corPos cx cy cor).2)) ∘ fun x ↦ (2:ℝ) • x) ⁻¹' usq =
    ∅ := by
  ext ⟨x,y⟩
  -- have hh:(corPos cx cy cor) = p := by rfl
  -- rw [hh] at h'
  simp
  have ext_h1 {a b :ℝ} : (a - b + 3) * 0.5 = x ∧ (a + b - 1) * 0.5 = y
    ↔ a = x+y-1 ∧ b = y-x + 2
    := by
    bound
  have ext_h2 {a b :ℝ} : (a + b + 4) * 0.5 = x ∧ (b - a + 6) * 0.5 = y
    ↔ a = x-y+1 ∧ b = x+y - 5
    := by
    bound
  simp [ext_h1,ext_h2]
  unfold usq square
  simp
  exact l2 h h'
  /-
  fin_cases cy
  . sorry
  . sorry
  . fin_cases cor <;> (
      simp [corPos]
      bound)
  . fin_cases cor <;> (
      simp [corPos]
      -- bound
      )
      -/


lemma twiddle_unions_2 {a b c d e : Set α} : (a ∪ b ∪ c ∪ d ∪ e) = a ∪(b ∪ c ∪ d ∪ e) := by
  simp only [union_assoc]

-- (⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) ∘ fun x ↦ 2 • x) ⁻¹'

lemma shift_sq {p : ℤ×ℤ} :
  (⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) ∘ fun x ↦ 2 • x) ⁻¹' usq
  = Ioo ((p.1:ℝ) / 2) ((p.1 +1) / 2) ×ˢ Ioo ((p.2:ℝ)/2) ((p.2+1)/2)  := by
  ext ⟨x,y⟩
  unfold usq square
  simp
  bound

lemma l4 {a b c d : Set α } : a = c ∧ b = d → (a∪b) = (c ∪ d) := by
  intro h
  simp_all only
lemma l5 {a b c d e : Set α } : a ∩ e = c  →  b ∩ e = d → (a∪b) ∩ e = (c ∪ d) := by
  intro h1 h2
  rw [union_inter_distrib_right]
  simp_all only

lemma l6 {a b c d: Set α } : a ⊔ (b ⊔ (c ⊔ d)) = a ∪ b ∪ c ∪ d := by
  simp only [← sup_assoc]
  rfl

lemma l7
(x y p1 p2 : ℝ)
(h1 : (x, y) ∈ Ioo 0.5 2.5 ×ˢ Ioo 0 3.5)
(h : p2 + 1 ≤ 0 ∨ 7 ≤ p2 ∨ 5 - p1 + 1 ≤ 0 ∨ 4 ≤ 5 - p1)
(h3 : p1 / 2 < x ∧ x < (p1 + 1) / 2)
(h4 : p2 / 2 < y ∧ y < (p2 + 1) / 2)
 : False := by
  simp at h1
  apply Or.elim h <;> (clear h)
  intro h
  have two_gt_z : 0<(2:ℝ) := by simp
  bound
  intro h
  apply Or.elim h  <;> (clear h)
  intro h
  bound
  intro h
  apply Or.elim h  <;> (clear h)
  bound
  intro h
  bound
  sorry
theorem subt_1
  (p : ℤ × ℤ )

  : (⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) ∘ fun x ↦ 2 • x) '' (d0 ∘ d0 '' pythagTree) ∩ usq =
  if 0 ≤ p.2 ∧ p.2 < 7 ∧ 0 ≤ 5 - p.1 ∧ 5 - p.1 < 4 then
    getTile (Piece.treePiece (Fin.ofNat' 7 p.2.toNat) (Fin.ofNat' 4 (5 - p.1).toNat) «Rot».left)
  else ∅ := by
  by_cases h : 0 ≤ p.2 ∧ p.2 < 7 ∧ 0 ≤ 5 - p.1 ∧ 5 - p.1 < 4
  . rw [if_pos h]
    sorry
  . rw [if_neg h]
    -- have hp := d00_pyt_in_rect
    apply Eq.trans (inter_preimage_image_inter usq _ _ _ _) (image_empty _)
    rw [shift_sq]
    apply Set.eq_empty_of_forall_not_mem
    intro ⟨x,y ⟩
    intro h
    rw [mem_inter_iff] at h
    obtain ⟨h1,h2⟩:= h
    #check Set.mem_of_subset_of_mem d00_pyt_in_rect
    rw [image_comp] at h1
    apply Set.mem_of_subset_of_mem d00_pyt_in_rect at h1
    simp at h2
    obtain ⟨h3,h4⟩ := h2
    simp only [Decidable.not_and_iff_not_or_not, Int.not_lt, Int.not_le] at h
    simp only [← Int.add_one_le_iff] at h
    -- have ZR_lt {a b :ℤ} : ((a:ℤ) :ℝ)<((b:ℤ) :ℝ )↔ (a:ℤ )<(b:ℤ ) := Int.cast_lt
    have ZR_le {a b :ℤ} : ((a:ℤ) :ℝ)≤ ((b:ℤ) :ℝ )↔ (a:ℤ )≤ (b:ℤ ) := Int.cast_le
    -- #check (Int.cast_lt : ((7:ℤ) :ℝ)<((6:ℤ) :ℝ )↔ (7:ℤ )<(6:ℤ ) )
    -- simp only [← ZR_lt] at h
    simp only [← ZR_le] at h
    -- simp at h
    simp only [Int.cast_add,Int.cast_sub,Int.cast_ofNat, Int.cast_zero,Int.cast_one] at h
    let p1:ℝ :=↑p.1
    have p1e : p1 = p.1 := by rfl
    let p2:ℝ :=↑p.2
    have p2e : p2 = p.2 := by rfl
    -- rw [← p1e] at h3
    -- simp_all [← p1e]
    -- simp [← p1e] at  h3
    simp only [←  p1e, ←  p2e] at h h1 h3 h4
    -- obtain ⟨ p1,p2⟩  := p
    --simp_all only [Prod.snd]
    bound
    bound


    simp_all only [Int.sub_nonneg, not_and, not_lt, d0, image_subset_iff, nsmul_eq_mul, Nat.cast_ofNat,
      Function.comp_apply, AffineEquiv.constVAdd_apply, vadd_eq_add, mem_inter_iff, mem_image, Prod.exists,
      Prod.mk.injEq, forall_exists_index, and_imp]
    intro x_1 x_2 x_3 x_4 a a_1 a_2 a_3
    subst a_2 a_1
    obtain ⟨fst, snd⟩ := p
    simp_all only
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    sorry
    sorry

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
    by_cases h' : (cy = 1 ∧ (corPos cx cy cor).1 > 4 ∧ (corPos cx cy cor).1 < 9)
    . simp only [if_pos h']
      exact (second_gen_squares cx cy cor h h')
    simp only [if_neg h']
    -- rw [pyt_is_union]
    let p := corPos cx cy cor
    -- let ⟨p1, p2⟩ := corPos cx cy cor
    rw [simp_subsq_pyt ((by rfl) : (p.1, p.2) = corPos cx cy cor)]
    trans  ⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) '' ((fun x ↦ (2:ℝ) • x)  ''
          (d0 '' (d0 '' pythagTree) ∪
              d0 '' (d1 '' pythagTree) ∪
            d1 '' (d0 '' pythagTree) ∪
          d1 '' (d1 '' pythagTree))) ∩ usq
    . nth_rw 1 [pyt_is_union]
      rw [← image_comp]
      rw [← Set.image_inter_preimage (⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) ∘ fun x ↦ (2:ℝ) • x) ]
      rw [union_assoc,union_assoc,union_assoc]
      unfold p
      rw [union_inter_left_empty (pyt_notbase_inter_base_empty h h')]
      rw [Set.image_inter_preimage (⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) ∘ fun x ↦ (2:ℝ) • x) ]
      unfold p
      nth_rw 5 [← image_comp]
      simp only [union_assoc]
    simp only [← image_comp,union_inter_distrib_right]
    /-
    have h : ⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) '' ((fun x ↦ 2 • x)
        '' pythagTree) ∩ usq =
      ⇑(AffineEquiv.constVAdd ℝ (ℝ × ℝ) (-↑p.1, -↑p.2)) '' ((fun x ↦ 2 • x)  ''
          (d0 '' (d0 '' pythagTree) ∪
              d0 '' (d1 '' pythagTree) ∪
            d1 '' (d0 '' pythagTree) ∪
          d1 '' (d1 '' pythagTree))) ∩
            usq := by
        rw [← image_comp, ← image_comp]
        apply preimage_inter_inter_image'
        nth_rw 1 [pyt_is_union]
        rw [twiddle_unions_2]
        rw [shift_sq]
        rw [union_inter_distrib_right]
        have h : (Ioo 3 4 ×ˢ Ioo 0 1 ∪ d0 '' Ioo 3 4 ×ˢ Ioo 0 1 ∪ d1 '' Ioo 3 4 ×ˢ Ioo 0 1) ∩
      Ioo ((p.1:ℝ) / 2) (((p.1:ℝ) + 1) / 2) ×ˢ Ioo ((p.2:ℝ ) / 2) ((↑p.2 + 1) / 2) = ∅ := by
          sorry
        rw [h]
        exact (empty_union _)
    rw [h]-/
    simp only [List.flatMap_cons]
    rw [List.flatMap_nil,List.append_nil]
    rw [←  ((by rfl) : (p.1, p.2) = corPos cx cy cor)]
    simp only [List.map_append]
    simp only [apply_ite (List.map getTile)]
    simp only [List.map]
    simp only [← Multiset.coe_add]
    simp only [Multiset.sup_add]
    simp only [l6]
    rw [image_union]
    apply (@l5 (ℝ×ℝ) _ _ _ _ usq)
    rw [image_union]
    apply (@l5 (ℝ×ℝ) _ _ _ _ usq)
    rw [image_union]
    apply (@l5 (ℝ×ℝ) _ _ _ _ usq)
    . simp only [apply_ite (fun x => Multiset.sup (Multiset.ofList x))]
      rw [Multiset.coe_singleton,Multiset.sup_singleton,Multiset.coe_nil, Multiset.sup_zero]
      rw [Set.bot_eq_empty]

      sorry
    -- apply (@l5 (ℝ×ℝ) _ _ _ _ usq)
    -- repeat (apply (@l5 (ℝ×ℝ) _ _ _ _ usq))
    -- ,image_union,image_union
    . sorry
    . sorry
    . sorry


theorem pieceMap_makes_piece (p : Piece) (cor : Cor):
  getTile p ∩ (corTransform cor '' usq) = (corTransform cor '' Multiset.sup (List.map getTile (pieceMap p cor))) := by
  sorry
