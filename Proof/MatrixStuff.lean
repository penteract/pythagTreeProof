import Mathlib
import Proof.Eqns
import Proof.CertProof
import Proof.TileAreaOpt
import Proof.Lemmas.List

theorem volFin {ps : List Piece} : vol ps ≠ ⊤ := by
  apply (ne_top_of_lt (b:=⊤))
  simp only [vol, Function.comp_apply]
  apply LE.le.trans_lt (MeasureTheory.measure_mono getTiles_in_usq)
  rw [vol_usq]
  exact ENNReal.one_lt_top


theorem vol_cors (ps : List Piece) : vol ps =
    vol (canon_cor_rot Cor.tl ps) / 4 +
    vol (canon_cor_rot Cor.br ps) / 4 +
    vol (canon_cor_rot Cor.bl ps) / 4 +
    vol (canon_cor_rot Cor.tr ps) / 4 := by
    rw [vol,Function.comp_apply]
    nth_rw 1 [vol_corners_sorted]
    simp only [Function.comp_apply]
    ring -- rearrange things due to the version I used to generate allparts

theorem vol_cors' (ps : List Piece) : vol' ps =
    vol' (canon_cor_rot Cor.tl ps) / 4 +
    vol' (canon_cor_rot Cor.br ps) / 4 +
    vol' (canon_cor_rot Cor.bl ps) / 4 +
    vol' (canon_cor_rot Cor.tr ps) / 4 := by
  have h:= @volFin ps
  simp_all only [vol_cors ps, vol']
  -- #check ENNReal.add_ne_top.mp h
  have ⟨h4',h4⟩ := (ENNReal.add_ne_top.mp h)
  have ⟨h3',h3⟩ := ENNReal.add_ne_top.mp h4'
  have ⟨ h1,h2⟩:= ENNReal.add_ne_top.mp h3'
  rw [← ENNReal.toReal_ofNat 4]
  simp only [← ENNReal.toReal_div]
  let tst := ENNReal.toReal_add h1 h2
  rw [← ENNReal.toReal_add h1 h2,
      ← ENNReal.toReal_add h3' h3,
      ← ENNReal.toReal_add h4' h4]

theorem vol_cors'' (ps : List Piece) : 4 * vol' ps =
    List.sum (List.map (fun cor => vol' (canon_cor_rot cor ps)) [Cor.tl, Cor.br, Cor.bl, Cor.tr]) := by
  rw [vol_cors']
  simp
  ring

theorem vol_full' : vol' [Piece.fullPiece] = 1 := by
  simp [getTiles,getTile,vol_usq,vol,vol']

theorem vol_empty' : vol' [] = 0 := by
  simp [getTiles,getTile,vol,vol']


-- theorem bigMat_is_system1 : bigMat
theorem fromAllParts_pyt_eqns {a b q} (h : (a,b,q) ∈ allparts) : Eqns.fromAllParts (a,b,q) ∈ pyt_eqns.toFinset := by
  unfold pyt_eqns Eqns.fromAllParts
  simp_all only [List.mem_toFinset, List.mem_map, Prod.mk.injEq, List.cons.injEq, and_true, Prod.exists,
    exists_eq_right_right]
  apply Exists.intro
  · apply Exists.intro
    · apply And.intro
      · exact h
      · apply And.intro
        · simp_all only
        · rfl

/-
def pyt_eqns_to_part ( e : pyt_eqns.toFinset) : List Piece × List (List Piece) × ℚ := by
  obtain ⟨x,xin ⟩ := e
  simp [pyt_eqns] at xin
  obtain ⟨a,b⟩ := xin -/

def cors := [Cor.tl, Cor.br, Cor.bl, Cor.tr]

theorem expand_mat {a b q} (h : (a,b,q) ∈ allparts) {hh}:
    bigMat (Subtype.mk (Eqns.fromAllParts (a,b,q)) hh /-(fromAllParts_pyt_eqns h)-/) x
    = (if a = ↑x then 4 else 0) + (List.map (fun y ↦ if canon_cor_rot y a = ↑x then -1 else 0) cors).sum
     := by
  unfold bigMat
  unfold pyt_eqns
  unfold Eqns.getMat
  simp only [Matrix.of_apply]
  unfold Eqns.fromAllParts
  simp only [List.map_cons, List.map_map, List.sum_cons]
  conv_lhs =>
    rhs
    rhs
    lhs
    ext y
    simp
  have ap := allParts_describes_pyt _ h
  simp only at ap
  rw [ap]
  rw [List.map_map]
  simp only [List.map_cons, List.map_nil] at ap
  rw [← cors]
  rfl

-- theorem redef_bigMat : bigMat = Matrix.of (fun f )


-- bigMat eqn x = ()
lemma a_in_allvars (h : (a, b, q) ∈ allparts) : a∈ Eqns.all_vars pyt_eqns := by
  unfold Eqns.all_vars
  simp only [List.mem_dedup, List.mem_map, List.mem_flatMap, Prod.exists, exists_and_right,
    exists_eq_right]
  unfold pyt_eqns
  unfold Eqns.fromAllParts
  simp only [List.mem_map, Prod.mk.injEq, Prod.exists, exists_eq_right_right]
  use 4
  apply Exists.intro
  apply And.intro
  use q
  use a
  use b
  exact List.mem_cons_self
def aps := allparts


lemma stuff_in_allvars (h : (a, b, q) ∈ allparts) : canon_cor_rot cor a ∈  Eqns.all_vars pyt_eqns := by
  unfold Eqns.all_vars
  simp only [List.mem_dedup, List.mem_map, List.mem_flatMap, Prod.exists, exists_and_right,
    exists_eq_right]
  unfold pyt_eqns
  unfold Eqns.fromAllParts
  simp only [List.mem_map, Prod.mk.injEq, Prod.exists, exists_eq_right_right]
  use -1
  use ((a, 4) :: List.map (fun x ↦ (x, -1)) b)
  apply And.intro
  use q
  use a
  use b
  apply List.mem_cons_of_mem
  have h : canon_cor_rot cor a ∈ b := by
    have hh := allParts_describes_pyt _ h
    simp only at hh
    rw [hh]
    apply List.mem_map_of_mem
    fin_cases cor <;> trivial
  simp_all only [List.mem_map, Prod.mk.injEq, and_true, exists_eq_right]

theorem subtype_eq {s : Finset ι} {a:ι} (b : s) (h :a∈ s) : a = b ↔ Subtype.mk a h = b := by
  rw [← Subtype.val_inj]


#check ∑ x, x
-- @Finset.sum ?m.8312 ?m.8312 ?m.8310 Finset.univ fun x ↦ x : ?m.8312

#check ∑ x∈ Finset.univ, x
-- @Finset.sum ?m.11450 ?m.11450 ?m.11452 ?m.11455 fun x ↦ x : ?m.11450


-- ∑ x, vol' ↑x * (List.map (Rat.cast ∘ fun y ↦ if canon_cor_rot y a = ↑x then -1 else 0) cors).sum



-- set_option maxRecDepth 200
theorem bigMat_vol_is_system :
    Matrix.mulVec (Matrix.map bigMat ((↑) : ℚ → ℝ ))
    (Subtype.restrict _ vol') = 0 := by
  have ap := allParts_describes_pyt
  simp only [Matrix.mulVec_eq_sum, op_smul_eq_smul]
  ext eqn
  obtain ⟨ e, einmap ⟩ := eqn
  unfold pyt_eqns at einmap
  simp only [List.mem_toFinset, List.mem_map, Prod.exists] at einmap
  obtain ⟨ a,b,q,abqinallparts,edef⟩ := einmap
  simp only [Pi.zero_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul,
    Pi.zero_apply]
  simp only [← edef]
  simp only [expand_mat abqinallparts]
  simp only [Rat.cast_add, Rat.cast_list_sum, List.map_map]
  simp only [Subtype.restrict_apply, apply_ite, Rat.cast_ofNat, Rat.cast_zero]
  simp only [left_distrib, mul_ite, mul_zero]
  -- have hh' := (a_in_allvars' (by sorry : [] ∈ Eqns.all_vars pyt_eqns))

  simp only [subtype_eq _ (List.mem_toFinset.mpr (a_in_allvars abqinallparts))]
  simp only [subtype_eq _ (List.mem_toFinset.mpr (stuff_in_allvars abqinallparts))]
  rw [Finset.univ_eq_attach]
  rw [Finset.sum_add_distrib]
  -- rw [← Finset.univ_eq_attach]
  simp only [← List.sum_map_mul_left]
  simp only [Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte, Function.comp_apply, apply_ite,
    Rat.cast_neg, Rat.cast_one, Rat.cast_zero, mul_neg, mul_one, mul_zero]
  rw [finset_list_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
  rw [mul_comm]
  rw [vol_cors'' a]
  unfold cors
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  ring



theorem mat_z {m n : Type } [Fintype m] [Fintype n] {A : Matrix m n ℝ} {x r : n → ℝ} {v : m → ℝ}
  (hAx : Matrix.mulVec A x = 0) (hqA : Matrix.vecMul v A = r) : dotProduct r  x = 0 := by
  rw [← hqA]
  rw [← Matrix.dotProduct_mulVec]
  rw [hAx]
  exact (dotProduct_zero _)

theorem thmst {s : Finset β} (f : β → ℝ) :(f∘(↑) : s→ ℝ ) = (Subtype.restrict _ f : { x // x ∈ s } → ℝ ) := by
  rfl

#check RingHom.map_vecMul

theorem allParts_makes_eqn_R :
    Matrix.vecMul (fun e => e.val.snd) (Matrix.map bigMat ((↑) : ℚ → ℝ )) =
    (fun v => Rat.cast (if v.val=[] then -Eqns.qEmpty else
              if v.val=[Piece.fullPiece] then -Eqns.qFull else
              if v.val ∈ init then 1 else 0 )) := by
  ext v
  have ap1 := congrFun (congrArg (Rat.castHom ℝ ∘ · ) allParts_makes_eqn) v
  simp only [Function.comp_apply] at ap1
  rw [RingHom.map_vecMul (Rat.castHom ℝ) bigMat (fun e => e.val.snd) v] at ap1
  rw [Rat.coe_castHom] at ap1
  exact ap1

-- theorem bigMat.map

theorem comp_both_args {h : α → β → γ} {f : δ→ α } {f' : δ → β} {x : ε}
   : h ((f ∘ g) x) ((f' ∘ g) x) = ((fun y => h (f y) (f' y)) ∘ g) x := by
   rfl

#check Finset.sum_subtype_of_mem

lemma sum_ss_mem_comp [AddCommMonoid M] (f : ι → M) {p : ι → Prop} [DecidablePred p] (h : ∀ x ∈ s, p x) :
    ∑ x ∈ s.subtype p, (f ∘ Subtype.val) x = ∑ x ∈ s, f x := by
  exact (Finset.sum_subtype_of_mem f h)

#check mat_z bigMat_vol_is_system allParts_makes_eqn_R

theorem vol_inits_val' : List.sum (List.map vol' init) = Eqns.qFull * vol' [Piece.fullPiece] + Eqns.qEmpty * vol' [] := by
  have h := mat_z bigMat_vol_is_system allParts_makes_eqn_R
  have fn_eq_comp :
    (fun (v : (Eqns.all_vars pyt_eqns).toFinset) ↦
      ((↑): ℚ→ℝ) (if v.val = [] then -Eqns.qEmpty else if ↑v = [Piece.fullPiece] then -Eqns.qFull else if ↑v ∈ init then 1 else 0) )
    = (fun v ↦ ↑(if v = [] then -Eqns.qEmpty else if v = [Piece.fullPiece] then -Eqns.qFull else if v ∈ init then 1 else 0)) ∘ Subtype.val := by rfl
  rw [fn_eq_comp] at h
  -- rw [← thmst] at h
  simp only [apply_ite Rat.cast, Rat.cast_neg, Rat.cast_one, Rat.cast_zero, ite_mul, neg_mul,
    one_mul, zero_mul] at h
  unfold dotProduct at h

  let l' : Finset ((Eqns.all_vars pyt_eqns).toFinset) := Finset.subtype _ eqn_parts
  -- #eval (fun (x : (Eqns.all_vars pyt_eqns).toFinset) => x ∈  l')
  have l_iff {x : (Eqns.all_vars pyt_eqns).toFinset} :
      x ∈ l' ↔ x.val = [] ∨ x.val = [Piece.fullPiece]∨ x.val ∈ init := by
    unfold l' eqn_parts
    simp only [List.toFinset_cons, Finset.mem_subtype, Finset.mem_insert, List.mem_toFinset]
  -- simp at
  rw [← Finset.sum_compl_add_sum l'] at h
  conv_lhs at h =>
    conv =>
      lhs
      simp only [Function.comp_apply, ite_mul, neg_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_of_false (by simp_all)]
      rw [Finset.sum_ite_of_false (by simp_all)]
      rw [Finset.sum_ite_of_false (by simp_all)]
      -- simp only [Finset.sum_const_zero]
      rfl
    -- simp only [Finset.sum_const_zero,Function.comp_apply, ite_mul, neg_mul, one_mul, zero_mul, zero_add]
    -- #check Finset.sum_subtype_of_mem
  rw [← thmst] at h
  simp only [comp_both_args] at h
  rw [sum_ss_mem_comp _ ] at h
  simp only [Finset.sum_const_zero, ite_mul, neg_mul, one_mul, zero_mul, zero_add] at h
  unfold eqn_parts at h

  rw [List.sum_toFinset _ eqn_parts_noDup] at h
  simp only [List.map_cons, ↓reduceIte, List.cons_ne_self, List.sum_cons] at h
  linear_combination (norm:=ring_nf) h
  ring_nf
  rw [sub_eq_add_neg]
  simp only [sum_neg_distrib, List.map_map]
  rw [← List.sum_map_add]
  unfold init
  simp [List.finRange_succ]
  exact eqn_parts_ss_allvars

theorem vol_inits_val : List.sum (List.map vol' init) = Eqns.qFull := by
  rw [vol_inits_val']
  rw [vol_full',vol_empty']
  ring_nf
