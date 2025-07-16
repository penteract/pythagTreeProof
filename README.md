This project formally proves that the area of the [Pythagoras tree](https://en.wikipedia.org/wiki/Pythagoras_tree_(fractal)) is a specific rational number:

```
theorem area_of_pythagoras_tree : MeasureTheory.volume pythagTree =
  12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979
  / 877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
```

pythagTree is defined in Proof/PythagTree.lean as the smallest set which is the union of a unit square and 2 appropriately rotated and scaled copies of itself.

'area_of_pythagoras_tree' depends on axioms: [propext, Classical.choice, Lean.ofReduceBool, Quot.sound]

The proof depends on Lean.ofReduceBool because it uses `native_decide` in Proof/CertProof.lean to show that a data structure represents a system of linear equations and that system of linear equations implies the above theorem.

#Building

If you don't already have lake installed (a tool which makes sure you're using the right versions of lean and mathlib), you will need to install [elan](https://github.com/leanprover/elan).

With that installed `lake build` should verify the proof. This may take some time. Rebuilding the proof takes up to 500 seconds on my machine, but it may take longer if you haven't already built Mathlib.
