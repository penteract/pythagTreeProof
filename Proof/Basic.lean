
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
  {ts_disj : Pairwise (Disjoint on (λ i => t i S))}
  {measurable_tis : ∀ i, (MeasurableSet (t i S))}
  {measurable_tifi : ∀ i, (MeasurableSet (t i (f i)))} -- The theorem is true without this assumption
                                                       -- (certainly when ι is finite) but I think that
                                                       -- would be a pain to prove
                                                       -- (keep cutting µ(A) = µ(A ∩ t i S) + µ(A \ t i S) until what you're left with has measure 0 )
  -- and A is a subset of S
  { asub : A ⊆ S}
  -- and t i (f i) combine make A (except for a measure zero bit)
  (aparts : ∀ i , (A ∩ t i S) =  t i (f i)) :
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
