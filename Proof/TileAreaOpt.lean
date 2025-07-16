import Mathlib
import Proof.TileArea

open Set

-- shrink the size of the DFA by quite a bit by consiering equivalent states
-- (picking canonical examples among lists of pieces that must have the same area)
-- Here we account for rotations, and note that all pieces which contain a solid square have the same area


#eval (canon_cor Cor.tl [Piece.treePiece 2 2 Rot.none])
#eval (canon_cor Cor.tl [Piece.treePiece 2 1 0, Piece.treePiece 5 0 1])
#eval (canon_cor Cor.tl [Piece.treePiece 3 0 1, Piece.treePiece 5 2 0])


theorem piece30_usq : (getTile ( Piece.treePiece 3 0 r) = usq) := by
  simp only [getTile]
  nth_rw 2 [← @thm_rot r]
  apply congrArg
  simp
  unfold pythagTree
  rw [← OrderHom.map_lfp]
  simp [treeFun_m,treeFun, -OrderHom.map_lfp ]
  transitivity (fun x ↦ (3, 0) + x) ⁻¹' Ioo 3 4 ×ˢ Ioo 0 1
  . intro ⟨x,y⟩
    unfold usq square
    simp only [NNReal.coe_one, zero_add, mem_prod, mem_Ioo, mem_preimage, Prod.mk_add_mk,
      lt_add_iff_pos_right, and_imp]
    bound
  exact Set.subset_union_right

theorem rot_canon_rot : (∃ r:Rot, rotTransform r '' getTiles ps = getTiles (canon_rot ps)) := by
  unfold canon_rot
  by_cases h : .fullPiece ∈ ps ∨ (∃ k, .treePiece 3 0 k ∈ ps)
  . simp only [if_pos h]
    use Rot.none
    simp only [rotTransform, «Rot».none, AffineEquiv.refl_apply, image_id']
    apply subset_antisymm
    transitivity usq
    exact getTiles_in_usq
    simp [getTiles,getTile]
    nth_rw 2 [getTiles]
    apply Multiset.le_sup
    unfold getTiles
    simp only [List.map_cons, List.map_nil, Multiset.coe_singleton, Multiset.sup_singleton,
      Multiset.mem_coe, List.mem_map]
    apply (Or.elim h)
    . intro h
      use Piece.fullPiece
    . intro ⟨r,h⟩
      use Piece.treePiece 3 0 r
      nth_rw 2 [getTile.eq_def]
      simp only
      simp [h,piece30_usq]
  . simp only [if_neg h]
    -- simp only [Option.some_get]
    simp only [List.map_cons]
    have ⟨a,h⟩  : ∃ a,
      (@List.max? _ (maxOfLe)  (List.map (fun r => canonical (rotList r ps)) [Rot.none, Rot.left, Rot.half, Rot.right]))
       = some a := by
       -- rw [Option.eq_some_of_isSome]
       use (List.foldl (@max _ (maxOfLe)) (canonical (rotList «Rot».none ps)) (List.map (fun r ↦ canonical (rotList r ps)) [«Rot».left, «Rot».half, «Rot».right]))
       rw [List.map_cons]
       rw [@List.max?_cons']
    have h' := @List.max?_mem _ _ maxOfLe (by
      intro a b
      simp only [maxOfLe, ite_eq_right_iff, ite_eq_left_iff]
      by_cases h : a ≤ b
      exact Or.inr (absurd h)
      exact Or.inl (Not.elim h)
      ) _ h
    let ⟨r,⟨h'',h'''⟩ ⟩ := List.mem_map.mp h'
    use r
    simp only [@List.max?_cons']
    rw [Option.get_some]
    simp only [List.map_cons,List.max?_cons'] at h
    rw [Option.some_inj] at h
    rw [h]
    rw [← h''']
    rw [getTiles_canonical]
    unfold getTiles
    unfold rotList
    rw [List.map_map]
    rw [Function.comp_def]
    simp only [← pieceMap_rot]
    simp only [Multiset.sup_coe,sup_eq_union]
    rw [foldr_distrib (f:= fun x => rotTransform r '' x) (op:=fun x1 x2 ↦ x1 ∪ x2)]
    rw [List.map_map]
    simp only [bot_eq_empty, image_empty,Function.comp_def]
    intro a b
    rw [image_union]


theorem volume_sort : MeasureTheory.volume (getTiles ps) = MeasureTheory.volume (getTiles (canon_rot ps)) := by
  have ⟨ r, h⟩ := @rot_canon_rot ps
  rw [← h]
  rw [rot_vol]


-- List.dropLast_append_getLast?
theorem getTiles_rem_empty : getTiles (rem_empty ps) = getTiles ps := by
  unfold rem_empty
  by_cases h : ps.getLast? = some Piece.emptyPiece
  . rw [if_pos h]
    unfold getTiles
    nth_rw 2 [← List.dropLast_append_getLast? _ (Option.mem_def.mpr h)]
    rw [List.map_append]
    simp only [Multiset.sup_coe]
    rw [List.foldr_append]
    nth_rw 2 [← Multiset.sup_coe]
    conv_rhs =>
      lhs
      simp only [List.map_cons, getTile, List.map_nil, Multiset.coe_singleton,
        Multiset.sup_singleton]
    simp only [bot_eq_empty]
  . rw [if_neg h]

theorem vol_corners_sorted (ps : List Piece) : MeasureTheory.volume (getTiles ps) =
    MeasureTheory.volume (getTiles (canon_cor_rot Cor.bl ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor_rot Cor.br ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor_rot Cor.tl ps))/4 +
    MeasureTheory.volume (getTiles (canon_cor_rot Cor.tr ps))/4 := by
  rw [vol_corners]
  unfold canon_cor canon_cor_rot
  simp only [getTiles_canonical,← volume_sort,getTiles_rem_empty]

theorem vol_full : MeasureTheory.volume (getTiles [Piece.fullPiece]) = 1 := by
  simp [getTiles,getTile,vol_usq]

theorem vol_empty : MeasureTheory.volume (getTiles []) = 0 := by
  simp [getTiles,getTile]
/-
#eval (canon_cor Cor.tl [Piece.treePiece 2 2 Rot.none])
#eval (canon_cor Cor.tl [Piece.treePiece 2 1 0, Piece.treePiece 5 0 1])
#eval (canon_cor Cor.tl [Piece.treePiece 3 0 1, Piece.treePiece 5 2 0])

#eval (canon_cor_rot Cor.tl [ Piece.treePiece 5 2 0])
#eval (canon_cor_rot Cor.tl [Piece.treePiece 1 1 3, Piece.treePiece 5 1 0])
#eval (canon_cor_rot Cor.tl [Piece.treePiece 2 2 3, Piece.treePiece 3 1 2])
#eval (canon_cor_rot Cor.br [Piece.treePiece 2 0 3, Piece.treePiece 4 0 0, Piece.trianglePiece 0])
#eval (canon_cor_rot Cor.br [Piece.treePiece 6 0 3, Piece.trianglePiece 0])
#eval (canon_cor_rot Cor.tl [Piece.treePiece 0 0 3, Piece.trianglePiece 3])
-/

theorem eqn_parts_noDup : ([]::[Piece.fullPiece]::init).Nodup := by
  decide

theorem setOf_prod {p : α → Prop} {q : β → Prop} : {x | p x} ×ˢ {y | q y} = {(x,y) | p x ∧ q y} := by
  rfl
theorem pyr_is_r : pythag_rect = rect (0,0) 7 4 := by
  unfold pythag_rect
  unfold rect Ioo
  rw [setOf_prod]
  simp only [zero_add,and_assoc]

theorem vol_pyt_is_vol_inits : MeasureTheory.volume pythagTree = List.sum (List.map vol init) := by
  -- rw [← List.sum_toFinset _ (by decide)]
  rw [volume_sum_pieces'
      (S := pythag_rect)
      (ι := Fin 7 × Fin 4)
      (B := usq)
      (t := fun p s => (AffineEquiv.constVAdd ℝ (ℝ×ℝ) ⟨p.1, p.2⟩ '' s))
      (fun p => getTiles [Piece.treePiece p.1 p.2 0] )
    ]
  . simp only [AffineEquiv.constVAdd_apply, vadd_eq_add, image_add_left, Prod.neg_mk,
    MeasureTheory.measure_preimage_add]
    unfold init
    rw [flatMap_map_product]
    rw [List.map_map]
    rw [← List.sum_toFinset _ (by decide)]
    rw [list_product_to_finset]
    simp only [List.toFinset_finRange, Function.comp_apply]
    rw [Finset.univ_product_univ]
    simp only [Function.uncurry]
    unfold vol
    simp [tsum_fintype]
  . rw [pyr_is_r]
    rw [vol_rect (Nat.ofNat_nonneg _)]
    exact ENNReal.ofReal_lt_top
  . simp
    intro a b ⟨x, y⟩
    unfold usq square pythag_rect
    have ha : (a.val : ℝ ) ≤ 6  := GCongr.natCast_le_natCast (Nat.le_sub_one_of_lt (Fin.isLt a))
    have hb : (b.val:ℝ) ≤ 3  := GCongr.natCast_le_natCast (Nat.le_sub_one_of_lt  (Fin.isLt b))
    simp only [NNReal.coe_one, zero_add, mem_preimage, Prod.mk_add_mk, mem_prod, mem_Ioo,
      lt_neg_add_iff_add_lt, add_zero, neg_add_lt_iff_lt_add, mem_setOf_eq, and_imp]
    have ha1 : 0≤ (a.val:ℝ) := Nat.cast_nonneg (a.val)
    have hb1 : 0≤ (b.val:ℝ) := Nat.cast_nonneg (b.val)
    bound
  . rw [pyr_is_r]
    rw [vol_rect (Nat.ofNat_nonneg _)]
    simp only [AffineEquiv.constVAdd_apply, vadd_eq_add, image_add_left, Prod.neg_mk,
      MeasureTheory.measure_preimage_add, vol_usq, ENNReal.tsum_one, ENat.card_eq_coe_fintype_card,
      Fintype.card_prod, Fintype.card_fin, Nat.reduceMul, Nat.cast_ofNat, ENat.toENNReal_ofNat,
      ENNReal.ofReal_eq_ofNat]
    ring
  . have h:= usqs_divide_rect 7 4
    simp only [usq]
    simp only [square_shift]
    simp_all [PairwiseDisjoint,Set.pairwise_univ]
  . intro i
    exact affine_measurable _ usq_measurable
  . intro i
    simp only []
    exact affine_measurable _ (getTiles_measurable _)
  . exact pyt_in_rect
  . unfold getTiles getTile
    -- simp? [Set.preimage_preimage]
    simp only [AffineEquiv.constVAdd_apply, vadd_eq_add, image_add_left, Prod.neg_mk, rotTransform,
      conj, one_div, AffineIsometryEquiv.toAffineEquiv_symm, neg_neg, List.map_cons,
      AffineEquiv.refl_apply, image_id', List.map_nil, Multiset.coe_singleton,
      Multiset.sup_singleton, preimage_inter, preimage_preimage, Prod.forall]
    intro a b
    simp [← add_assoc,Prod.mk_zero_zero]
