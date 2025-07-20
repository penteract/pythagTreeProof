import Mathlib

-- Stuff needed by ProofCert.lean and also by other files

open List

namespace Eqns

variable {α : Type}

def fromAllParts : (α× (List α) × ℚ) → (List (α × ℚ) × ℚ)  := (fun x ↦
          match x with
          | (a, b, q) => ((a, 4) :: List.map (fun x ↦ (x, -1)) b, q))

def qFull:  ℚ := 12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979/877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
def qEmpty:  ℚ := 11746934357449947552830291532943152290456105411186011016486060686616960007897677336844906536622212814156785625/877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093


def toCoeffs (l : List (List (α × ℚ) × ℚ)) : List (α × ℚ) := l.flatMap (fun (a,q) => a.map (fun (x,p) => (x,q*p)))


-- evaluate a linear equation of variabes and coefficients at a function assigning values to variables
def evalWith (f:α → ℝ ) (l : List (α × ℚ)) : ℝ  := List.sum (List.map (fun y => y.2 * f y.1 ) l)
theorem evalWithCons : evalWith f ((a,q)::l) = q*f a + evalWith f l := by
  unfold evalWith
  simp

theorem mulEq (l : List (α × ℚ)) (q :ℚ ) (h : evalWith f l = 0)
    : evalWith f (List.map (fun (v,k)=>(v,q*k)) l) = 0 := by
  unfold evalWith at *
  simp only [map_map]
  conv_lhs =>
    enter [1,1,x]
    simp only [Function.comp_apply, Rat.cast_mul]
    rw [mul_assoc]
  rw [List.sum_map_mul_left]
  rw [h]
  exact (mul_zero _)

theorem appendEq : evalWith f (l1++l2) = evalWith f l1 + evalWith f l2 := by
  unfold evalWith at *
  rw [List.map_append, List.sum_append]

theorem appendEq_z (h1 : evalWith f l1 = 0) (h2 : evalWith f l2 = 0) : evalWith f (l1++l2) = 0 := by
  unfold evalWith at *
  rw [List.map_append, List.sum_append]
  simp [h1,h2]


theorem permEq (p : List.Perm l l') : evalWith f l = evalWith f l' :=
  List.Perm.sum_eq (List.Perm.map _ p)

theorem sortEq {f} {l : (List (α × ℚ)) } [LT α] [hdec: DecidableRel (· ≤ · : (α×ₗℚ) → (α×ₗℚ) → Prop)]
    : evalWith f (List.mergeSort l (fun x y => @decide (toLex x ≤ toLex y) (hdec x y)) ) = evalWith f l :=
  permEq (List.mergeSort_perm l _)

theorem mergeOneEq : evalWith f ((x,q)::(x,q')::l)  = evalWith f ((x,q+q')::l) := by
  simp only [evalWithCons]
  rw [← add_assoc,← right_distrib,Rat.cast_add]


def mergeFold [DecidableEq α ] : ( List (α × ℚ)) →  List (α×ℚ) -- := match l with
  | List.cons (a ,q) (List.cons (b,q') tl) => if a=b then mergeFold ((a,q+q') :: tl) else (a,q)::mergeFold ((b,q')::tl)
  | other => other
termination_by  l => l.length

def mergeFold_acc [DecidableEq α ] (acc : List (α × ℚ)) : (List (α × ℚ)) →  List (α×ℚ) -- := match l with
  | List.cons (_ ,0) tl => mergeFold_acc acc tl
  | List.cons (a ,q) (List.cons (b,q') tl) => if a=b then mergeFold_acc acc ((a,q+q') :: tl) else mergeFold_acc ((a,q)::acc) ((b,q')::tl)
  | other => (acc) ++ other
termination_by  l => l.length
/-
theorem mergeFold_eq_acc [DecidableEq α] {l:List (α × ℚ)} : mergeFold_acc xs l = xs.reverse ++ mergeFold l := by
  sorry
-/
theorem list_length_induction (p : List α → Prop) (hind : ∀ l:List α, (∀ l':List α, l'.length < l.length → p l')→ p l) (l:List α) : p l := by
  have h : ∀ n:ℕ , ∀ l : List α, l.length≤n → p l := by
    intro n
    induction n with
      | zero =>
        intro l
        intro lz
        apply (hind l)
        intro _
        intro h
        have h':= (Nat.lt_of_lt_of_le h lz)
        contradiction
      | succ n ih =>
        intro l h
        cases Nat.le_or_eq_of_le_add_one h with
        | inl h => exact (ih _ h)
        | inr h =>
          apply hind l
          simp only [h]
          exact (fun l' lenlen => ih l' (Nat.le_of_lt_add_one lenlen))
  exact (h l.length l le_rfl)

theorem mergeEq [DecidableEq α ] {l : List (α × ℚ) }: evalWith f l = evalWith f (mergeFold l) := by
  refine (list_length_induction (p:= fun l => evalWith f l = evalWith f (mergeFold l)) ?_ l)
  intro l
  intro h
  match l with
  | List.cons (a ,q) (List.cons (b,q') tl) =>
      rw [mergeFold.eq_1]
      --unfold evalWith at *
      by_cases he : a=b
      . simp_all only [length_cons, ↓reduceIte]
        rw [← h ((b, q + q') :: tl) ]
        exact mergeOneEq
        simp
      . simp_all only [length_cons, ↓reduceIte]
        rw [evalWithCons]
        nth_rw 2 [evalWithCons]
        rw [← h ((b, q') :: tl)]
        simp
  | List.cons x nil => unfold mergeFold ; simp
  | List.nil => unfold mergeFold ; simp

theorem mergeEq_acc [DecidableEq α ] {l : List (α × ℚ) }: evalWith f (xs++l) = evalWith f (mergeFold_acc xs l) := by
  refine (list_length_induction (p:= fun l => ∀ xs', evalWith f (xs'++l) = evalWith f (mergeFold_acc xs' l)) ?_ l) xs
  intro l
  intro h
  unfold  mergeFold_acc
  split <;> intro xs'
  case h_1 tl =>
    simp only [Int.ofNat_eq_coe, CharP.cast_eq_zero, Rat.mk_den_one, Int.cast_zero]
    rw [appendEq]

    rw [evalWithCons]
    ring_nf
    rw [← appendEq]
    rw [h]
    simp
  case h_2 a q b q' tl hh =>
    by_cases he : a=b
    . simp_all only [length_cons, ↓reduceIte]
      rw [← h ((b, q + q') :: tl) ]
      rw [appendEq,appendEq]
      rw [mergeOneEq]
      simp
    . simp_all only [length_cons, ↓reduceIte]
      rw [appendEq]
      rw [evalWithCons]
      rw [← h ((b, q') :: tl)]
      rw [appendEq]
      nth_rw 2 [evalWithCons]
      ring
      simp
  case h_3 =>
    simp only

theorem eval_toCoeffs  (l : List (List (α × ℚ) × ℚ) ) (f : α → ℝ)
    (h : ∀ x ∈ l, evalWith f  x.1 = (0:ℝ) )
    : evalWith f (toCoeffs l) = 0  := by
  unfold toCoeffs
  induction l with
  | nil => unfold evalWith
           simp
  | cons hd tl tail_ih =>
    simp
    apply appendEq_z
    . apply mulEq
      exact h (_) (by simp)
    simp at tail_ih
    apply tail_ih
    intro a b a_1
    simp_all only [mem_cons, forall_eq_or_imp, Prod.forall]
    obtain ⟨fst, snd⟩ := hd
    obtain ⟨left, right⟩ := h
    simp_all only
    apply right
    · exact a_1

theorem eval_toCoeffs_merged [DecidableEq α ] [LT α] [DecidableRel (· < · : α → α → Prop)] (l : List (List (α × ℚ) × ℚ) ) (f : α → ℝ)
    (h : ∀ x ∈ l, evalWith f  x.1 = (0:ℝ) )
    : evalWith f (mergeFold_acc [] (mergeSort (toCoeffs l)
          (fun x y => @decide (toLex x ≤ toLex y) (Prod.Lex.instDecidableRelOfDecidableEq x y))))
      = 0 := by
  rw [← mergeEq_acc]
  rw [appendEq_z]
  . unfold evalWith ; simp
  rw [sortEq (hdec:= _)]
  rw [eval_toCoeffs l f h]
