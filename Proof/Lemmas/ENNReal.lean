import Mathlib

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
