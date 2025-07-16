import Mathlib
import Proof.Tiles
import Proof.SquareDivision
import Proof.Rotations
import Proof.Basic
open Set

def getTiles (ps : List Piece) : Set R2 := Multiset.sup (List.map getTile ps)

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

/-
lemma ll : getTile hd ⊔ (getTiles tl) ∩ ⇑(corTransform cor) '' usq =
    getTile hd ∪ (getTiles tl) ∩ ⇑(corTransform cor) '' usq := by
    rw [Set.sup_eq_union]
    sorry
-/

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

theorem getTiles_canonical : getTiles (canonical ll) =getTiles ll := getTiles_list_finset _ _ (canonical_preserves_elements ll)

def canon_cor (cor : Cor) (ps : List Piece) := canonical (List.flatMap (fun p => pieceMap p cor) ps)

/-
lemma vol_part (cor:Cor) (ps:List Piece) :
    MeasureTheory.volume (getTiles (canon_cor cor ps))/4 =
    MeasureTheory.volume (getTiles ps ∩ (corTransform cor '' usq)) := by
  rw [← @vol_quater _ cor]
  unfold canon_cor
  rw [getTiles_list_finset _ _ (canonical_preserves_elements _)]
  rw [pieceMap_makes_pieces]
-/
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



theorem usq_measurable : MeasurableSet usq := by
  unfold usq square
  exact MeasurableSet.prod measurableSet_Ioo measurableSet_Ioo

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
    rw [corTransform_same]
    apply affine_measurable
    exact (getTiles_measurable _)
  . exact getTiles_in_usq
  simp only
  intro i
  rw [pieceMap_makes_pieces ps]
  unfold canon_cor
  rw [getTiles_list_finset _ _ (canonical_preserves_elements _)]

-- #eval! (List.head (canon_cor Cor.tl [Piece.treePiece 2 2 Rot.none]) sorry)
#eval (canon_cor Cor.tl [Piece.treePiece 2 2 Rot.none])
#eval (canon_cor Cor.tl [Piece.treePiece 2 1 0, Piece.treePiece 5 0 1])
#eval (canon_cor Cor.tl [Piece.treePiece 3 0 1, Piece.treePiece 5 2 0])

def rotList (r :Rot) (ps : List Piece) : List Piece :=  List.map (rotatep r) ps

-- List.max?_mem
def canon_rot (ps : List Piece) : List Piece :=
  if .fullPiece ∈ ps ∨ (∃ k, .treePiece 3 0 k ∈ ps) then [.fullPiece] else
    Option.get (@List.max? _ (maxOfLe)  (List.map (fun r => canonical (rotList r ps)) [Rot.none, Rot.left, Rot.half, Rot.right]))
    /- [(rotList Rot.none ps) , (rotList Rot.left ps),
                            (rotList Rot.half ps) , (rotList Rot.right ps)]-/
        (by
          simp only [List.map_cons, List.max?_cons', Option.isSome_some]
        )
    /- @min _ (minOfLe) (rotList Rot.none ps) (@min _ (minOfLe) (rotList Rot.left ps)
    (@min _ (minOfLe) (rotList Rot.half ps) (@min _ (minOfLe) (rotList Rot.right ps) )) -/


lemma foldr_distrib {l:List α } {f : α → α}  {op : α → α → α} (h :∀ a b,  f (op a b) = op (f a) (f b)) : f (List.foldr op e l) = List.foldr (op) (f e) (List.map f l) := by
  induction l with
  | nil => simp
  | cons a b ih =>
    simp [ih,h]


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

def rem_empty (ps : List Piece) : List Piece :=
  if (List.getLast? ps) = some Piece.emptyPiece then List.dropLast ps else ps

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



def canon_cor_rot (cor : Cor) (ps : List Piece) := rem_empty (canon_rot (List.flatMap (fun p => pieceMap p cor) ps))

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

def init : List (List Piece) :=
  (List.finRange 7).flatMap
    (fun i => (List.finRange 4).map
      (fun j => [Piece.treePiece i j 0]))

theorem eqn_parts_noDup : ([]::[Piece.fullPiece]::init).Nodup := by
  decide

noncomputable def vol := MeasureTheory.volume ∘ getTiles

noncomputable def vol' (ps: List Piece) : ℝ  := ENNReal.toReal (vol ps)



theorem uncurry_comp_mk : Function.uncurry f ∘ Prod.mk a = f a := by
  rfl

theorem flatMap_map_product : (List.flatMap (fun i ↦ List.map (f i) s) t) = List.map (Function.uncurry f) (List.product t s) := by
  rw [List.product.eq_1]
  rw [List.map_flatMap]
  simp only [List.map_map,uncurry_comp_mk]

theorem list_product_to_finset [DecidableEq α] {a : List α } [DecidableEq β] {b : List β}
    : (List.product a b).toFinset = a.toFinset ×ˢ b.toFinset := by
  apply Finset.Subset.antisymm
  . intro ⟨x,y⟩ h
    simp_all
  . intro ⟨x,y⟩ h
    simp_all

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

  -- exact (List.Nodup.of_cons (List.Nodup.of_cons eqn_parts_noDup) )

/-
nth_rewrite 1 [volume_sum_pieces
    (S := usq)
     (A := getTiles ps)
      (t:= fun i s => corTransform i '' s)
       (fun c => getTiles (canon_cor c ps))]
  -/
