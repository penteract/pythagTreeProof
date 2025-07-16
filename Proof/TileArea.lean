import Mathlib
import Proof.Tiles
import Proof.TileDefs
import Proof.SquareDivision
import Proof.Rotations
import Proof.Basic
import Proof.Lemmas.List
open Set

theorem getTiles_in_usq : getTiles ps ⊆ usq := by
  simp only [getTiles, Multiset.sup_coe, sup_eq_union, bot_eq_empty]
  induction ps with
  | nil => simp
  | cons h t ih =>
    simp
    apply (And.intro)
    . unfold getTile
      match h with
      | .emptyPiece => simp
      | .fullPiece => simp
      | .trianglePiece r =>
        simp only
        rw [← @thm_rot r]
        apply Set.image_mono
        exact tri_in_sq
      | .treePiece a b r =>
        simp only
        nth_rw 2 [← @thm_rot r]
        apply Set.image_mono
        exact inter_subset_right
    exact ih

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


-- proofs about cannonical

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

lemma canonical_preserves_elements (l : List Piece) : forall a, a ∈ (canonical l) ↔ a ∈ l := by
  unfold canonical
  intro a
  transitivity
  exact List.mem_dedup
  exact (List.Perm.mem_iff (List.mergeSort_perm l (· ≤ · )))

theorem getTiles_canonical : getTiles (canonical ll) = getTiles ll := getTiles_list_finset _ _ (canonical_preserves_elements ll)



-- working through the assumptions needed for volume_sum_pieces

lemma measurable_sq_corners (i:Cor) : MeasurableSet ((fun i s ↦ ⇑(corTransform i) '' s) i usq) := by
  simp only
  rw [corTransform_same]
  exact affine_measurable _ usq_measurable

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

theorem d0_preserve_measurable {s :  Set (ℝ×ℝ)} (h : MeasurableSet s) : MeasurableSet (d0 '' s) := by
  rw [d0_eq_d0aff]
  exact (affine_measurable _ h)
theorem d1_preserve_measurable {s :  Set (ℝ×ℝ)} (h : MeasurableSet s) : MeasurableSet (d1 '' s) := by
  rw [d1_eq_d1aff]
  exact (affine_measurable _ h)

theorem treeFun_measure_preserving {s : Set (ℝ×ℝ)} (h : MeasurableSet s) : MeasurableSet (treeFun s) := by
  unfold treeFun
  apply MeasurableSet.union
  apply MeasurableSet.union
  exact (d0_preserve_measurable h)
  exact (d1_preserve_measurable h)
  exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo

theorem pyt_measurable : MeasurableSet pythagTree := by
  unfold pythagTree
  rw [fixedPoints.lfp_eq_sSup_iterate]
  unfold iSup
  apply MeasurableSet.iUnion
  intro n
  induction n with
   | zero => simp
   | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (treeFun_measure_preserving ih)
  unfold treeFun_m
  rw [OmegaCompletePartialOrder.ωScottContinuous_iff_monotone_map_ωSup]
  --unfold OmegaCompletePartialOrder.Continuous
  unfold CompleteLattice.instOmegaCompletePartialOrder -- I shouldn't do this, but it works for now
  simp only [iSup_eq_iUnion, OrderHom.coe_mk, OmegaCompletePartialOrder.Chain.map_coe,
    Function.comp_apply, exists_prop]
  and_intros
  . exact treeFun_monotone
  intro c
  ext x
  unfold treeFun
  repeat rw [image_iUnion]
  simp only [mem_union,mem_iUnion,exists_or,exists_const]

theorem getTile_Measurable (p:Piece) : MeasurableSet (getTile p) := by
  match p with
    | .fullPiece =>
      simp only [getTile]
      exact usq_measurable
    | .emptyPiece => simp [getTile]
    | .trianglePiece r =>
        simp only [getTile]
        exact affine_measurable _ (tri_measurable)
    | .treePiece a b c =>
      simp only [getTile]
      apply affine_measurable
      apply MeasurableSet.inter
      apply affine_measurable
      exact pyt_measurable
      exact usq_measurable
theorem getTiles_measurable (ps: List Piece ) : MeasurableSet (getTiles ps) := by
  unfold getTiles
  simp only [Multiset.sup_coe, sup_eq_union, bot_eq_empty,List.foldr_map]
  induction ps with
  | nil => simp
  | cons h t ih => simp; exact (MeasurableSet.union (getTile_Measurable _) ih)
theorem vol_corners (ps : List Piece) : MeasureTheory.volume (getTiles ps) =
    MeasureTheory.volume (getTiles (canon_cor Cor.bl ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor Cor.br ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor Cor.tl ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor Cor.tr ps))/4 := by
  nth_rewrite 1 [volume_sum_pieces
    (S := usq) (A := getTiles ps) (t:= fun i s => corTransform i '' s) (fun c => getTiles (canon_cor c ps))]
  . rw [tsum_fintype]
    unfold Finset.univ
    simp only [Cor.fintype, Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert,
      Finset.mem_insert, reduceCtorEq, Finset.mem_mk, Multiset.mem_singleton, or_self,
      not_false_eq_true, Finset.sum_insert, Finset.sum_mk, Multiset.map_singleton,
      Multiset.sum_singleton]
    simp only [vol_quater]
    simp only [add_assoc]
  . simp [usq,vol_sq]
  . apply iSup_le
    exact @cor_sq_ss
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
    rw [corTransform_same]
    apply affine_measurable
    exact (getTiles_measurable _)
  . exact getTiles_in_usq
  simp only
  intro i
  rw [pieceMap_makes_pieces ps]
  unfold canon_cor
  rw [getTiles_list_finset _ _ (canonical_preserves_elements _)]
