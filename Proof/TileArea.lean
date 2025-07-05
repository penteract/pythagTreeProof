import Mathlib
import Proof.Tiles
import Proof.SquareDivision
import Proof.Basic
open Set



def getTiles (ps : List Piece) : Set R2 := Multiset.sup (List.map getTile ps)


/-
lemma ll : getTile hd ⊔ (getTiles tl) ∩ ⇑(corTransform cor) '' usq =
    getTile hd ∪ (getTiles tl) ∩ ⇑(corTransform cor) '' usq := by
    rw [Set.sup_eq_union]
    sorry
-/


#check List.foldl_op_eq_op_foldr_assoc

-- List.foldl_op_eq_op_foldr_assoc.{u} {α : Type u} {op : α → α → α} [ha : Std.Associative op] {l : List α} {a₁ a₂ : α} :
 --  op (List.foldl op a₁ l) a₂ = op a₁ (List.foldr (fun x1 x2 ↦ op x1 x2) a₂ l)

lemma foldr_comm_append [Std.Associative op]  [Std.Commutative op]:
  (List.foldr (fun x1 x2 ↦ op x1 x2) e (t1++t2))  =
  (List.foldr (fun x1 x2 ↦ op x1 x2) e (t2++t1)) := by
    simp only [← Multiset.coe_fold_r]
    simp only [← Multiset.coe_add]
    rw [add_comm]

lemma foldy [Std.Associative op]  [Std.Commutative op]:
  List.foldl (fun x1 x2 ↦ op x1 x2) (List.foldr (fun x1 x2 ↦ op x1 x2) e t1) tt =
  List.foldr (fun x1 x2 ↦ op x1 x2) (List.foldr (fun x1 x2 ↦ op x1 x2) e tt) t1
   := by
    rw [List.foldl_eq_foldr]
    rw [← List.foldr_append]
    rw [← List.foldr_append]
    rw [foldr_comm_append]

theorem pieceMap_makes_pieces {cor : Cor} (ps : List Piece) :
  getTiles ps ∩ (corTransform cor '' usq)
  = (corTransform cor '' getTiles (List.flatMap (fun p => pieceMap p cor) ps)):= by
  have h := pieceMap_makes_piece
  unfold getTiles
  induction ps with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, Multiset.sup_coe, -- Set.sup_eq_union, Set.bot_eq_empty,
        List.foldr_cons, List.flatMap_cons, List.map_append, List.foldr_append]
      simp only [← Multiset.sup_coe]
      simp only [Set.sup_eq_union]
      rw [Set.union_inter_distrib_right,ih]
      rw [Multiset.sup_coe]
      rw [Set.sup_eq_union]
      rw [pieceMap_makes_piece]
      rw [← image_union]
      rw [← @List.foldl_op_eq_op_foldr_assoc (Set R2) (· ∪ ·)]
      apply congrArg
      simp only [Multiset.sup_coe, sup_eq_union, bot_eq_empty, union_empty]
      rw [foldy]


lemma getTiles_list_dedup (l:List Piece):
    getTiles l = getTiles (l.dedup) := by
  unfold getTiles
  apply le_antisymm <;> (
    simp only [Multiset.sup_le]
    intro b h
    apply Multiset.le_sup
    simp_all only [Multiset.mem_coe, List.mem_map, List.mem_dedup]
  )

lemma getTiles_list_finset (l1:List Piece) (l2 : List Piece) (h : forall a, a ∈ l1 ↔ a ∈ l2):
    getTiles l1 = getTiles l2 := by
  unfold getTiles
  apply le_antisymm <;> (
    simp only [Multiset.sup_le]
    intro b h
    apply Multiset.le_sup
    simp_all only [Multiset.mem_coe, List.mem_map]
  )

def canonical (l : List Piece) : List Piece:= (List.mergeSort l (· ≤ · )).dedup

lemma canonical_preserves_elements (l : List Piece) : forall a, a ∈ (canonical l) ↔ a ∈ l := by
  unfold canonical
  intro a
  transitivity
  exact List.mem_dedup
  exact (List.Perm.mem_iff (List.mergeSort_perm l (· ≤ · )))

def canon_cor (cor : Cor) (ps : List Piece) := canonical (List.flatMap (fun p => pieceMap p cor) ps)

lemma vol_part (cor:Cor) (ps:List Piece) :
    MeasureTheory.volume (getTiles (canon_cor cor ps))/4 =
    MeasureTheory.volume (getTiles ps ∩ (corTransform cor '' usq)) := by
  rw [← @vol_quater _ cor]
  unfold canon_cor
  rw [getTiles_list_finset _ _ (canonical_preserves_elements _)]
  rw [pieceMap_makes_pieces]

/-
lemma ennrlem1 (a:ENNReal) : a = 4 * (a / 4) := by
  cases' a
  rw [ENNReal.top_div_of_ne_top]
  rw [ENNReal.mul_top]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  simp only [ne_eq, ENNReal.ofNat_ne_top, not_false_eq_true]
  rw [← ENNReal.coe_ofNat 4]
  -- #check ENNReal.coe_div (sorry : (OfNat.ofNat 4 : ENNReal) ≠ 0)
  conv_rhs =>
    rhs
    rw [← ENNReal.coe_div _]
    rfl
    rw [NNReal.coe_ne_zero]
  have h : ↑x✝ / ↑(OfNat.ofNat 4) = ↑
    :=  ENNReal.coe_div _
  rw [ENNReal.coe_div (sorry : (OfNat.ofNat 4 : ENNReal) ≠ 0)]
  rw [ENNReal.toNNReal_div]

  sorry-/


lemma measurable_sq_corners (i:Cor) : MeasurableSet ((fun i s ↦ ⇑(corTransform i) '' s) i usq) := by
  simp
  unfold usq
  rw [sq_cors]
  unfold square
  exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo

theorem pyt_measurable : MeasurableSet pythagTree := by
  sorry

theorem tri_measurable : MeasurableSet triangle := by
  unfold triangle
  rw [Set.setOf_and]
  rw [Set.setOf_and]
  apply IsOpen.measurableSet
  apply IsOpen.inter
  have h : {a : ℝ × ℝ | 0 < a.1} = Ioi 0 ×ˢ univ := by
    ext ⟨x,y⟩
    simp
  rw [h]
  apply (IsOpen.prod)
  exact isOpen_Ioi
  exact isOpen_univ
  apply IsOpen.inter
  have h : {a : ℝ × ℝ | 0 < a.2} = univ ×ˢ Ioi 0 := by
    ext ⟨x,y⟩
    simp
  rw [h]
  apply (IsOpen.prod)
  exact isOpen_univ
  exact isOpen_Ioi
  apply isOpen_lt
  exact continuous_add
  exact continuous_const

theorem getTile_Measurable (p:Piece) : MeasurableSet (getTile p) := by
  match p with
    | .fullPiece =>
      simp only [getTile]
      unfold usq square
      exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo
    | .emptyPiece => simp [getTile]
    | .trianglePiece r =>
        simp only [getTile]
        exact affine_measurable _ (tri_measurable)
    | .treePiece a b c =>
      simp [getTile]
      unfold getTile

theorem vol_counts (ps : List Piece) : MeasureTheory.volume (getTiles ps) =
    MeasureTheory.volume (getTiles (canon_cor Cor.bl ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor Cor.br ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor Cor.tl ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor Cor.tr ps))/4 := by
  nth_rewrite 1 [volume_sum_pieces
    (S := usq) (A := getTiles ps) (t:= fun i s => corTransform i '' s) (fun c => getTiles (canon_cor c ps))]
  . rw [tsum_fintype]
    unfold Finset.univ
    simp [Cor.fintype]
    simp only [vol_quater]
    simp only [add_assoc]
  . simp [usq,vol_sq]
  . apply iSup_le
    exact @cor_ss_sq
  . simp
    simp only [vol_usq, vol_quater,
      ENNReal.tsum_const, ENat.card_eq_coe_fintype_card,
      ENat.toENNReal_coe]
    rw[mul_one_div]
    rw [square_has_4_corners]
    simp only [Nat.cast_ofNat]
    rw [ENNReal.div_self] <;> simp
  . exact cor_disj
  . exact measurable_sq_corners
  . intro i
    simp only
    rw [← triCor_corners i]
    apply MeasurableSet.inter
    exact triangle_measurable
    exact (measurable_sq_corners i)
  . exact tri_in_sq
  exact triCor_corners
  /-simp [vol_part]
  nth_rewrite 1 [volume_sum_pieces
    (S := usq) (A := getTiles ps) (t:= fun i s => corTransform i '' s) (fun c => getTiles (canon_cor c ps))]
  -/
  sorry
