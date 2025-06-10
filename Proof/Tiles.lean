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
    sorry


theorem pieceMap_makes_piece (p : Piece) (cor : Cor):
  getTile p ∩ (corTransform cor '' usq) = (corTransform cor '' Multiset.sup (List.map getTile (pieceMap p cor))) := by
  sorry
