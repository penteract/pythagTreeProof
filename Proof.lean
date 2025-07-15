-- This module serves as the root of the `Proof` library.
-- Import modules here that should be built as part of the library.
import Proof.Basic
import Proof.SquareDivision
import Proof.TileArea
-- import Proof.TriangleTest
import Proof.CertProof
import Proof.MatrixStuff
-- Test files:
-- TriangleTest
-- Statement
-- Questions
-- Neat
-- Neat2
-- Neat3
lemma toReal_obv (bnz : b ≠ 0) (bnt : b≠ ⊤ ): ENNReal.toReal a = ENNReal.toReal b → a = b := by
  intro h
  have hh := (ENNReal.toReal_eq_toReal_iff _ _).mp h
  simp_all

theorem ENNReal_sum_fin_not_top {l : List ENNReal} (lfin : ∀ x∈ l, x<⊤) : List.sum l ≠ ⊤ := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      simp_all only [List.mem_cons, or_true, implies_true, ne_eq, forall_const, forall_eq_or_imp, List.sum_cons,
        ENNReal.add_eq_top, or_false]
      obtain ⟨left, right⟩ := lfin
      apply Aesop.BuiltinRules.not_intro
      intro a
      subst a
      simp_all only [lt_self_iff_false]
theorem ENNReal_sum_fin {l : List ENNReal} (lfin : ∀ x∈ l, x<⊤) : ENNReal.toReal (List.sum l) = List.sum (List.map ENNReal.toReal l) := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
      simp_all
      rw [← ih]
      have hh := ENNReal_sum_fin_not_top (lfin.2)
      rw [ENNReal.toReal_add (ne_of_lt lfin.1) hh]

-- open SquareDiv
theorem area_of_pythagoras_tree : MeasureTheory.volume pythagTree =
  12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979
  / 877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093 := by

  rw [vol_pyt_is_vol_inits]
  apply toReal_obv
  simp
  apply ne_of_lt (ENNReal.div_lt_top (ENNReal.ofNat_ne_top) (OfNat.ofNat_ne_zero _))
  rw [ENNReal_sum_fin]
  simp only [List.map_map, ENNReal.toReal_div, ENNReal.toReal_ofNat]
  have h:=vol_inits_val
  unfold vol' at h
  erw [h]
  simp [qFull]
  simp
  intro x
  intro h
  exact (Ne.lt_top volFin)


#print d0.eq_1
#print d1.eq_1
#print treeFun.eq_1
#print treeFun_m.eq_1
#print pythagTree.eq_1
#check area_of_pythagoras_tree
#print axioms area_of_pythagoras_tree
