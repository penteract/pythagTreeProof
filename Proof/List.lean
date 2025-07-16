import Mathlib

theorem sum_neg_distrib [AddCommGroup M] {xs : List M} : - List.sum xs = List.sum (List.map (fun x => -x) xs) := by
  exact AddMonoidHom.map_list_sum (-AddMonoidHom.id M) xs

theorem finset_list_sum [AddCommMonoid r] [Fintype s] (f : s → β → r)
   : ∑ x ∈ s',  List.sum (List.map (f x) l) = List.sum (List.map (fun y => ∑ x∈ s', f x y) l) := by
  induction l with
  | nil => simp
  | cons h t ih=>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib]
    simp_all
