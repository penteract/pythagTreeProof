import Mathlib
open OrderHom
open Real
open Set

def d0 (p : (ℝ × ℝ)) := ((p.1 - p.2) * 0.5 , (p.1 + p.2) * 0.5 + 1 )

def d1 (p : (ℝ × ℝ)) := ((p.1 + p.2 + 1) * 0.5 , (p.2 - p.1 + 3) * 0.5)

def unit_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 }

def treeFun (s : Set (ℝ × ℝ)) : Set (ℝ × ℝ) := d0 '' s ∪ d1 '' s ∪ unit_sq


theorem constx_mono {β} {x:α} [Preorder α] [Preorder β]: Monotone (Function.const β x) := by
  intro _ _ _
  rfl

theorem treeFun_monotone : Monotone (treeFun) := Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const
def treeFun_m : Set (ℝ × ℝ) →o Set (ℝ × ℝ) := ⟨ treeFun , treeFun_monotone⟩

def pythagTree := lfp treeFun_m

theorem pyt_area : MeasureTheory.volume pythagTree = 12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979 / 877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
 := by
  sorry
