import Mathlib

-- Stuff needed by ProofCert.lean and also by other files

open List

namespace Eqns

variable {α β : Type}
-- variable (ll : List (List (α × ℚ) × ℚ)) -- represents a list of equations and coefficients of said equations
-- variable (toEqn : β → List (α × ℚ) )
-- variable (f : α → ℝ )

def all_vars [DecidableEq α] (ll : List (List (α × ℚ) × ℚ)) : List α := dedup ((flatMap Prod.fst ll ).map Prod.fst)

-- def Mat (ll : List (List (α × ℚ) × ℚ)) := Matrix { e // e∈ ll} {v // v ∈ (all_vars ll)}  ℚ

/-
def getMat (ll : List (List (α × ℚ) × ℚ)) :  Matrix { e // e∈ ll} {v // v ∈ (all_vars ll)} ℚ := Matrix.of
  (fun e v => sum (e.val.fst.map (fun (a,q) =>if a=v then q else 0 )))
-/
def getMat [DecidableEq α] (ll : List (List (α × ℚ) × ℚ)) :  Matrix ll.toFinset (all_vars ll).toFinset ℚ := Matrix.of
  (fun e v => sum (e.val.fst.map (fun (a,q) =>if a=v then q else 0 )))



def fromAllParts : (α× (List α) × ℚ) → (List (α × ℚ) × ℚ)  := (fun x ↦
          match x with
          | (a, b, q) => ((a, 4) :: List.map (fun x ↦ (x, -1)) b, q))

def qFull:  ℚ := 12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979/877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
def qEmpty:  ℚ := 11746934357449947552830291532943152290456105411186011016486060686616960007897677336844906536622212814156785625/877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093


theorem vecMulToList [DecidableEq α] (l : List (List (α × ℚ) × ℚ)) (h : Nodup l) :
  Matrix.vecMul (fun e => e.val.2) (getMat l)
  = fun v => List.sum (l.map (fun (((a:List (α × ℚ )),(q:ℚ) ))
                => List.sum (a.map fun ((v':α),(r:ℚ)) => if v'=v.val then q*r else (0:ℚ)))) := by
  rw [Matrix.vecMul_eq_sum]
  ext v
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply]
  unfold getMat
  simp only [ Matrix.of_apply, smul_eq_mul]
  rw [← List.sum_toFinset _ h]
  simp only [← List.sum_map_mul_left]
  simp only [mul_ite, mul_zero]
  nth_rw 2 [← Finset.sum_finset_coe]
  rfl
  -- simp only [Finset.sum_subtype_of_mem (fun x => (map (fun b ↦ if b.1 = ↑v then (x).2 * b.2 else 0) (x).1).sum )]
  -- rw [smul_eq_mul]
  -- simp only [Finset.univ_eq_attach, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

def toCoeffs (l : List (List (α × ℚ) × ℚ)) : List (α × ℚ) := l.flatMap (fun (a,q) => a.map (fun (x,p) => (x,q*p)))

/-
lemma tistFnAlt [DecidableEq α] (l : List (List (α × ℚ) × ℚ)) : (fun (v : { x // x ∈ (all_vars l).toFinset }) =>
    List.sum (l.map (fun (((a:List (α × ℚ )),(q:ℚ) )) =>
      List.sum (a.map fun ((v':α),(r:ℚ)) => if v'=v.val then q*r else (0:ℚ)))))
  = fun v => List.sum (List.map (fun (v',r) => if v'=v.val then r else (0:ℚ))  (toCoeffs l))
    := by
  sorry -/

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

theorem appendEq (h1 : evalWith f l1 = 0) (h2 : evalWith f l2 = 0) : evalWith f (l1++l2) = 0 := by
  unfold evalWith at *
  rw [List.map_append, List.sum_append]
  simp [h1,h2]

theorem sortEq {f} {l : (List (α × ℚ)) } [LE α]  [DecidableRel (· ≤ · : α → α → Prop)]
    : evalWith f (List.mergeSort l (fun x y => (x ≤ y )) ) = evalWith f l := by
  unfold evalWith
  rw [List.Perm.sum_eq (List.Perm.map _ (List.mergeSort_perm l _))]

theorem mergeOneEq : evalWith f ((x,q)::(x,q')::l)  = evalWith f ((x,q+q')::l) := by
  unfold evalWith
  simp only [map_cons, sum_cons, Rat.cast_add]
  rw [← add_assoc,← right_distrib]

def mergeFold [DecidableEq α ] : ( List (α × ℚ)) →  List (α×ℚ) -- := match l with
  | List.cons (a ,q) (List.cons (b,q') tl) => if a=b then mergeFold ((a,q+q') :: tl) else (a,q)::mergeFold ((b,q')::tl)
  | other => other
termination_by  l => l.length

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

theorem eval_toCoeffs  (l : List (List (α × ℚ) × ℚ) ) (f : α → ℝ)
    (h : ∀ x ∈ l, evalWith f  x.1 = (0:ℝ) )
    : evalWith f (toCoeffs l) = 0  := by
  unfold toCoeffs
  induction l with
  | nil => unfold evalWith
           simp
  | cons hd tl tail_ih =>
    simp
    apply appendEq
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

theorem eval_toCoeffs_merged [DecidableEq α ] [LE α] [DecidableRel (· ≤ · : α → α → Prop)] (l : List (List (α × ℚ) × ℚ) ) (f : α → ℝ)
    (h : ∀ x ∈ l, evalWith f  x.1 = (0:ℝ) )
    : evalWith f (mergeFold (mergeSort (toCoeffs l))) = 0  := by
  rw [← mergeEq]
  rw [sortEq]
  rw [eval_toCoeffs l f h]
