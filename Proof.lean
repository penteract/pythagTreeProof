-- This module serves as the root of the `Proof` library.
-- Import modules here that should be built as part of the library.
import Proof.Lemmas.ENNReal
-- import Proof.Basic
-- import Proof.SquareDivision
-- import Proof.TileArea
-- import Proof.TriangleTest
import Proof.CertProof
import Proof.MatrixStuff


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
  simp [Eqns.qFull]
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
