
import Mathlib
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

open Set Real MeasureTheory intervalIntegral MeasurableSet

open scoped Real NNReal ENNReal



-- open NFA

variable {α ι : Type*}

variable {m : MeasureSpace α}
variable {S A : Set α}

#check DFA.toNFA_correct

#check MeasureTheory.Measure.m_iUnion

#check MeasurableSet[m.toMeasurableSpace]
#check MeasureSpace
#check MeasurableSpace

-- theorem linear_prod_fun
-- open LinearEquiv
theorem linear_cont (g : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ)) : Continuous g := by
  --aesop
  let e := ContinuousLinearEquiv.finTwoArrow ℝ ℝ
  have h : g =  g ∘ₗ e.toLinearMap ∘ₗ e.symm.toLinearMap := by
    simp_all only [ContinuousLinearEquiv.symm_toLinearEquiv, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id, e]
  rw [h]
  apply Continuous.comp (LinearMap.continuous_on_pi (g ∘ₗ e.toLinearMap))
  exact e.continuous_invFun

--open MeasureTheory
-- theorem affine_Measurable (f : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ)) : MeasurableEmbedding f := by
--   sorry
theorem affine_measurable (f : (ℝ × ℝ) ≃ᵃ[ℝ] (ℝ × ℝ)) {s : Set (ℝ×ℝ)} (h : MeasurableSet s ) : MeasurableSet (f '' s) := by
  let g := f.symm
  have g_coe_coe_eq_coe : (g : (ℝ × ℝ) → (ℝ × ℝ)) = (g : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ)) := AffineEquiv.coe_toAffineMap g
  have hh : Measurable g := by
    apply Continuous.measurable
    rw [g_coe_coe_eq_coe]
    apply AffineMap.continuous_linear_iff.mp
    exact (linear_cont g.linear)
  rw [← AffineEquiv.preimage_symm f s]
  exact hh h

-- A , B , C , D ⊆ S
--variable {I : Finset ι}
--variable {iotaFinite : Fintype ι}
variable [Countable ι]
variable {t : ι → Set α → Set α}

--open Filter

theorem volume_sum_pieces (f : ι → Set α)
  -- If  S has finite volume
  {sfinite : volume S < ⊤ }
  -- and t i  are a collection of transformations that map S to pieces of itself
  -- (S is a rep-tile)
  {ssubs : ⋃ i, t i S ⊆ S}
  {smakes : volume S = ∑' i, volume (t i S)} -- alternatively, S =ᵐ[volume] ⋃ i, t i S
  {ts_disj : Pairwise (Function.onFun Disjoint (λ i => t i S))}
  {measurable_tis : ∀ i, (MeasurableSet (t i S))}
  {measurable_tifi : ∀ i, (MeasurableSet (t i (f i)))} -- The theorem is true without this assumption
                                                       -- (certainly when ι is finite) but I think that
                                                       -- would be a pain to prove
                                                       -- (keep cutting µ(A) = µ(A ∩ t i S) + µ(A \ t i S) until what you're left with has measure 0 )
  -- and A is a subset of S
  { asub : A ⊆ S}
  -- and t i (f i) combine make A (except for a measure zero bit)
  {aparts : ∀ i , (A ∩ t i S) =  t i (f i)} :
  -- then the volume of the pieces is the volume of A
  volume A = ∑' i, volume (t i (f i)) := by
  --simp
  --intro sFinite subs smakes t_s_disj asub tf_meas aparts
  have lem_tifisubtiS : ∀ i, t i (f i) ⊆ t i S := by
    intro i
    rw [← aparts i]
    exact inf_le_right
  have lem : ∑' i, volume (t i (f i)) = volume (⋃ i, t i (f i)) := by
    apply eq_comm.mp
    --rw [← tsum_fintype]
    --apply @measure_iUnion _ α m.toMeasurableSpace volume _ _
    apply measure_iUnion
    apply (pairwise_disjoint_mono ts_disj)
    exact lem_tifisubtiS

    trivial
  rw [lem]
  -- have : _ := calc
  --   (⋃ i, t i (f i)) = (⋃ i, A ∩ t i S) := by simp [aparts]
  --   _ = A ∩ (⋃ i, t i S) := by simp [inter_iUnion]
  rw [calc
    (⋃ i, t i (f i)) = (⋃ i, A ∩ t i S) := by simp [aparts]
    _ = A ∩ (⋃ i, t i S) := by simp [inter_iUnion]]
  have mutis: MeasurableSet (⋃ i, t i S) := by
    apply MeasurableSet.iUnion
    simp [measurable_tis]
  have saetis : volume (S \ ⋃ i, t i S) = 0 := by
    have vsum : volume (S ∩ ⋃ i, t i S) + volume (S \ ⋃ i, t i S) = volume S  := by
      --apply eq_comm.mp
      apply measure_inter_add_diff
      exact mutis
    have : volume (S ∩ ⋃ i, t i S) ≤ volume S := by
      calc volume (S ∩ ⋃ i, t i S)
          ≤ volume (S ∩ ⋃ i, t i S) + volume (S \ ⋃ i, t i S) :=
              le_add_right (le_refl (volume (S ∩ ⋃ i, t i S)))
        _ = volume S := vsum
    calc
      volume (S \ ⋃ i, t i S)
        = volume S - volume (S ∩ ⋃ i, t i S) := by
          rw [← vsum]
          apply eq_comm.mp
          apply ENNReal.add_sub_cancel_left
          apply ne_of_lt
          calc volume (S ∩ ⋃ i, t i S)
              ≤ volume S := this
            _ < ⊤ := sfinite
      _ = volume S - volume (⋃ i, t i S) := by rw [inter_eq_self_of_subset_right ssubs]
      _ = volume S - ∑' i, volume (t i S) := by
        rw [measure_iUnion]
        trivial
        trivial
      --_ = volume S - ∑ i, volume (t i S) := by rw [← tsum_fintype]
      _ = volume S - volume S := by rw [smakes]
      _ = 0 := by simp
  have  mz : volume (A \ ⋃ i, t i S) = 0 := by
    apply le_antisymm
    swap
    exact bot_le
    rw [← saetis]
    apply (volume.mono)
    apply Set.diff_subset_diff_left
    exact asub
  calc
    volume A = volume (A ∩ ⋃ i, t i S) + volume (A \ ⋃ i, t i S) := by
      apply eq_comm.mp
      apply (MeasureTheory.measure_inter_add_diff₀)
      simp [mutis]
    _ = volume (A ∩ ⋃ i, t i S) := by
      rw [mz]
      ring


-- TODO: same as above , but with finset ι and
--useful: exists_measurable_superset_of_null
--        measure_inter_add_diff₀

/-

theorem inter_biUnion {ι α : Type*} {s : Set ι} (hs : s.Nonempty) (f : ι → Set α) (t : Set α) :
    ⋃ i ∈ s, t ∩ f i = t ∩ (⋃ i ∈ s, f i) := by
  haveI : Nonempty s := hs.to_subtype
  rw [Set.biUnion_eq_iUnion]
  simp [← Set.inter_iUnion]

theorem volume_sum_pieces_finite [fini: Finite ι] (f : ι → Set α)
  --{cara : MeasureTheory.OuterMeasure.IsCaratheodory}
  -- If  S has finite volume
  {sfinite : volume S < ⊤ }
  -- and t i  are a collection of transformations that map S to pieces of itself
  -- (S is a rep-tile)
  {ssubs : ⋃ i, t i S ⊆ S}
  {smakes : volume S = ∑' i, volume (t i S)} -- alternatively, S =ᵐ[volume] ⋃ i, t i S
  {ts_disj : Pairwise (Disjoint on (λ i => t i S))} -- consider Set.PairwiseDisjoint
  {measurable_tis : ∀ i, (MeasurableSet (t i S))}
  -- {measurable_tis : ∀ i, (MeasureTheory.OuterMeasure.IsCaratheodory (toOuterMeasure m.volume) (t i S))}
  /-
  {measurable_tifi : ∀ i, (MeasurableSet (t i (f i)))} -- The theorem is true without this assumption
                                                       -- (certainly when ι is finite) but I think that
                                                       -- would be a pain to prove
                                                       -- (keep cutting µ(A) = µ(A ∩ t i S) + µ(A \ t i S) until what you're left with has measure 0 )
  -/
  -- and A is a subset of S
  { asub : A ⊆ S}
  -- and t i (f i) combine make A (except for a measure zero bit)
  {aparts : ∀ i , (A ∩ t i S) =  t i (f i)} :
  -- then the volume of the pieces is the volume of A
  volume A = ∑' i, volume (t i (f i)) := by
  --simp
  --intro sFinite subs smakes t_s_disj asub tf_meas aparts
  have lem_tifisubtiS : ∀ i, t i (f i) ⊆ t i S := by
    intro i
    rw [← aparts i]
    exact inf_le_right
  have lem : ∑' i, volume (t i (f i)) = volume (⋃ i, t i (f i)) := by
    apply eq_comm.mp
    --rw [← tsum_fintype]
    --apply @measure_iUnion _ α m.toMeasurableSpace volume _ _
    --have? : _ + _ = _ using fini
    rw [tsum_eq_finsum]
    rw [← finsum_mem_univ]
    -- @[simp] (how do I use this?)
    let C (s : Set ι) : Prop := volume (⋃ i∈ s, t i (f i)) = ∑ᶠ i∈s, volume (t i (f i))
    rw [← Set.Finite.induction_to_univ (C:=C) ∅]
    rw [Set.biUnion_univ]
    simp [C]

    intro s nottop p
    let i := Set.Nonempty.some (Set.nonempty_compl.mpr nottop)
    have h := Set.Nonempty.some_mem (Set.nonempty_compl.mpr nottop)
    use i
    apply And.intro
    exact h
    simp only [C]
    simp [C] at p
    simp only [← aparts]
    rw [inter_biUnion]
    rw [Set.biUnion_insert]
    -- rw [Set.biSum_insert]
    rw [finsum_mem_insert _ h]
    -- simp [← aparts]

    -- rw [measure_inter_add_diff (A∩(⋃ i_1 ∈ insert i s, t i_1 (f i_1)) ) (measurable_tis i)]
    rw [←  (measure_inter_add_diff _ (measurable_tis i))]
    simp only [inter_assoc,union_inter_cancel_left]
    simp [inter_diff_assoc,union_diff_left]
    nth_rewrite 2 [← Finset.set_biUnion_singleton i (fun j => t j S)]
    #check biUnion_diff_biUnion_eq (s:=s) (t:={i}) (f:=(fun j => t j S))
    rw [biUnion_diff_biUnion_eq (s:=s) (t:={i}) (f:=(fun j => t j S)) _]
    simp [mem_inter_iff, mem_union, and_congr_left_iff, true_or, and_true]
    -- #check (MeasureTheory.OuterMeasure.isCaratheodory_iff _).mp (measurable_tis i)
    -- rw [ ]

    apply measure_iUnion
    apply (pairwise_disjoint_mono ts_disj)
    exact lem_tifisubtiS

    trivial
  rw [lem]
  -- have : _ := calc
  --   (⋃ i, t i (f i)) = (⋃ i, A ∩ t i S) := by simp [aparts]
  --   _ = A ∩ (⋃ i, t i S) := by simp [inter_iUnion]
  rw [calc
    (⋃ i, t i (f i)) = (⋃ i, A ∩ t i S) := by simp [aparts]
    _ = A ∩ (⋃ i, t i S) := by simp [inter_iUnion]]
  have mutis: MeasurableSet (⋃ i, t i S) := by
    apply MeasurableSet.iUnion
    simp [measurable_tis]
  have saetis : volume (S \ ⋃ i, t i S) = 0 := by
    have vsum : volume (S ∩ ⋃ i, t i S) + volume (S \ ⋃ i, t i S) = volume S  := by
      --apply eq_comm.mp
      apply measure_inter_add_diff
      exact mutis
    have : volume (S ∩ ⋃ i, t i S) ≤ volume S := by
      calc volume (S ∩ ⋃ i, t i S)
          ≤ volume (S ∩ ⋃ i, t i S) + volume (S \ ⋃ i, t i S) :=
              le_add_right (le_refl (volume (S ∩ ⋃ i, t i S)))
        _ = volume S := vsum
    calc
      volume (S \ ⋃ i, t i S)
        = volume S - volume (S ∩ ⋃ i, t i S) := by
          rw [← vsum]
          apply eq_comm.mp
          apply ENNReal.add_sub_cancel_left
          apply ne_of_lt
          calc volume (S ∩ ⋃ i, t i S)
              ≤ volume S := this
            _ < ⊤ := sfinite
      _ = volume S - volume (⋃ i, t i S) := by rw [inter_eq_self_of_subset_right ssubs]
      _ = volume S - ∑' i, volume (t i S) := by
        rw [measure_iUnion]
        trivial
        trivial
      --_ = volume S - ∑ i, volume (t i S) := by rw [← tsum_fintype]
      _ = volume S - volume S := by rw [smakes]
      _ = 0 := by simp
  have  mz : volume (A \ ⋃ i, t i S) = 0 := by
    apply le_antisymm
    swap
    exact bot_le
    rw [← saetis]
    apply (volume.mono)
    apply Set.diff_subset_diff_left
    exact asub
  calc
    volume A = volume (A ∩ ⋃ i, t i S) + volume (A \ ⋃ i, t i S) := by
      apply eq_comm.mp
      apply (MeasureTheory.measure_inter_add_diff₀)
      simp [mutis]
    _ = volume (A ∩ ⋃ i, t i S) := by
      rw [mz]
      ring
-/

/-
theorem volume_sum_piecesInf (f : ι → Set S) :
  -- If  S has finite volume
  (volume S < ⊤ ) →
  -- and t i  are a collection of transformations that map S to pieces of itself
  -- (S is a rep-tile)
  ⋃ i:ι, t i S ⊆ S → volume S = ∑' i:ι, volume (t i S) → Pairwise (Disjoint on (λ i:ι => t i S)) →
  -- and A is a subset of S
  A ⊆ S →
  -- and t i (f i) combine make A (except for a measure zero bit)
  (∀ i:ι, (MeasurableSet (t i (f i)))) →
  (∀ i : ι, (A ∩ t i S) =  t i (f i)) →
  -- then the vol
  volume A = ∑' i:ι, volume (t i (f i)) := by
  --simp
  intro h aparts
  sorry
-/


-- theorem mScale : MeasureTheory.volume s = 0 ∧
-- #check tacticVolume_tac
