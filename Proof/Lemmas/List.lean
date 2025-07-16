import Mathlib


lemma foldr_distrib {l:List α } {f : α → α}  {op : α → α → α} (h :∀ a b,  f (op a b) = op (f a) (f b)) : f (List.foldr op e l) = List.foldr (op) (f e) (List.map f l) := by
  induction l with
  | nil => simp
  | cons a b ih =>
    simp [ih,h]

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

lemma foldr_comm_append [Std.Associative op]  [Std.Commutative op]:
  (List.foldr (fun x1 x2 ↦ op x1 x2) e (t1++t2))  =
  (List.foldr (fun x1 x2 ↦ op x1 x2) e (t2++t1)) := by
    simp only [← Multiset.coe_fold_r]
    simp only [← Multiset.coe_add]
    rw [add_comm]

-- more specific
lemma foldy [Std.Associative op]  [Std.Commutative op]:
  List.foldl (fun x1 x2 ↦ op x1 x2) (List.foldr (fun x1 x2 ↦ op x1 x2) e t1) tt =
  List.foldr (fun x1 x2 ↦ op x1 x2) (List.foldr (fun x1 x2 ↦ op x1 x2) e tt) t1
   := by
    rw [List.foldl_eq_foldr]
    rw [← List.foldr_append]
    rw [← List.foldr_append]
    rw [foldr_comm_append]
