import Mathlib
import Proof.Eqns
-- import Proo


def es : List (List (ℕ × ℚ) × ℚ) := [
  ([(0,1),(1,1),(2,8)],1/2),
  ([(0,1),(1,-1),(2,2)],1/2)
]

open Eqns
/-
def getMat (ll : List (List (α × ℚ) × ℚ)) :  Matrix { e // e∈ ll} {v // v ∈ (all_vars ll)} ℚ := Matrix.of
  (fun e v => sum (e.val.fst.map (fun (a,q) =>if a=v then q else 0 )))
-/

#eval (getMat es) (Subtype.mk (es.head (by simp [es])) (by simp) ) (Subtype.mk 1 (by decide))
noncomputable def f : α → ℝ := sorry

-- Assumptions
theorem f2one : f 2 = -1 := by sorry

theorem es_is_system : Matrix.mulVec (Matrix.map (getMat es) ((↑) : ℚ → ℝ )) (Subtype.restrict _ f) = 0 := by
  sorry

#eval (Matrix.vecMul (fun e => e.val.snd) (getMat es) )
  (Subtype.mk 1 (by decide))
-- = (fun v => if v.val=0 then 1 else if v.val=2 then 5 else 0)
#eval (Matrix.vecMul (fun e => e.val.snd) (getMat es) )
  (Subtype.mk 1 (by decide))
#eval (Matrix.vecMul (fun e => e.val.snd) (getMat es) )
  (Subtype.mk 0 (by decide))
#eval (Matrix.vecMul (fun e => e.val.snd) (getMat es) )
  (Subtype.mk 2 (by decide))
#eval (3+3 :ℕ )

theorem list_nodup_sum_subtype (l : List α) : {x // x∈ l} =  {x // x ∈ (List.toFinset l)} := by
  simp only [mem_toFinset]
-- @Membership.mem α (Finset α) Finset.instMembership l.toFinset a
-- @Membership.mem α (Finset α) Finset.instMembership l.toFinset x

/- theorem thmm (l : List ℕ ): l.toFinset.sum f = 0 := by
  sorry -/
theorem es_makes_eqn : Matrix.vecMul (fun e => e.val.snd) (getMat es) = (fun v => if v.val=0 then 1 else if v.val=2 then 5 else 0) := by
  with_unfolding_all decide

-- variable {m n : Type } [Fintype m] [Fintype n] {A : Matrix m n ℚ } {x r : n → ℚ } {v : m → ℚ }
theorem mat_z {m n : Type } [Fintype m] [Fintype n] {A : Matrix m n ℝ} {x r : n → ℝ} {v : m → ℝ}
  (hAx : Matrix.mulVec A x = 0) (hqA : Matrix.vecMul v A = r) : dotProduct r  x = 0 := by
  rw [← hqA]
  rw [← Matrix.dotProduct_mulVec]
  rw [hAx]
  exact (dotProduct_zero _)

lemma ratCast_eq (a b : ℚ) : a = b ↔ (a : ℝ) = (b : ℝ) := by simp only [Rat.cast_inj]

variable {m n : Type } [Fintype m]  {A : Matrix m n ℚ } {x r : n → ℚ } {v : m → ℚ }
/-
@Eq ℝ (∑ i, (f ∘ Subtype.val) i * (g ∘ Subtype.val) i) (∑ x ∈ s, f x * g x) : Prop

@Finset.sum { x // x ∈ s } ℝ Real.instAddCommMonoid Finset.univ fun i ↦ (f ∘ Subtype.val) i * (g ∘ Subtype.val) i : ℝ
-/

theorem mq_cast_r {i : n} : (Rat.cast :ℚ→ℝ ) (Matrix.vecMul v A i) = Matrix.vecMul (Rat.cast ∘ v) (Matrix.map A Rat.cast) i := by
  -- #check RingHom.map_vecMul (Rat.castHom ℝ)  A v i
  exact RingHom.map_vecMul (Rat.castHom ℝ) _ _ _

theorem nodup_es : Nodup es := by
  sorry

#check Finset.sum_toList --_ nodup_es
#check @Finset.sum

theorem ttt {s : Finset β} : { x // x ∈ s } = s := by
 rfl



-- theorem fseq {r} [rm : AddCommMonoid r] {s : Finset α} (f : α → r) : @Finset.sum { x // x ∈ s } r rm Finset.univ (f ∘ (↑))
--         = @Finset.sum α r rm s f := by
--   simp [-Finset.univ_eq_attach]
--   exact Finset.sum_coe_sort s f


theorem thmst {s : Finset β} (f : β → ℝ) :(f∘(↑) : s→ ℝ ) = (Subtype.restrict _ f : { x // x ∈ s } → ℝ ) := by
  rfl

-- Finset.sum
#check @Finset.sum
theorem thmdot {s : Finset β } (f g : β → ℝ) : dotProduct (f∘(↑) : s→ ℝ )  (g ∘ (↑)) =
    @Finset.sum β  ℝ _ s (fun x => f x * g x) := by
  unfold dotProduct
  simp only [Function.comp_apply]
  rw [Finset.sum_coe_sort s (fun x => f x * g x)]
  -- alternative proof:
  -- rw [← Finset.sum_coe_sort s (fun x => f x * g x)]
  -- rfl

theorem thmdot2 {s : Finset β } (f g : β  → ℝ) : dotProduct (Subtype.restrict _ f : s → ℝ ) (Subtype.restrict _ g : s→ ℝ) =
    @Finset.sum β ℝ _ s (fun x => f x * g x) := by
  rw [← Finset.sum_coe_sort s (fun x => f x * g x)]
  rfl

theorem nodup_av : Nodup (all_vars es) := by sorry
theorem f0five : f 0 = 5:= by
  have es2 := es_makes_eqn
  apply congrArg (fun f => ((↑):ℚ→ℝ) ∘ f ) at es2
  rw [funext_iff] at es2
  simp only [Function.comp_apply] at es2
  simp only [mq_cast_r] at es2
  rw [← funext_iff] at es2
  have h := mat_z es_is_system es2
  linear_combination (norm:=skip) h
  -- unfold dotProduct

  /-
  simp only [add_zero]
  simp only [apply_ite Rat.cast, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero, ite_mul, one_mul, zero_mul]
  -/
  have lem : (fun (x:{x //x∈ (all_vars es).toFinset}) ↦ (Rat.cast:ℚ→ ℝ ) (if x.val = 0 then 1 else if x.val = 2 then 5 else 0)) =
              (fun (x:ℕ ) => (Rat.cast:ℚ→ℝ ) (if x = 0 then 1 else if x = 2 then 5 else 0)) ∘ Subtype.val := by
      rfl
  rw [lem]
  rw [← thmst]
  rw [thmdot]
  simp only [apply_ite Rat.cast, Rat.cast_one, Rat.cast_ofNat, Rat.cast_zero, ite_mul, one_mul, zero_mul]
  have h : (fun x ↦ if x = 0 then f x else if x = 2 then 5 * f x else 0) = (fun x ↦ (if x = 0 then f x else 0) + (if x = 2 then 5 * f x else 0)) := by
    ext x
    simp_all only
    split
    next h_1 =>
      subst h_1
      simp_all only [OfNat.zero_ne_ofNat, ↓reduceIte, add_zero]
    next h_1 => simp_all only [zero_add]
  rw [h]
  rw [Finset.sum_add_distrib]
  simp only [add_zero, Finset.sum_ite_eq', mem_toFinset]
  unfold all_vars es
  rw [f2one]
  simp



def sumZero (f : α → ℝ ) (e : List (α × ℚ)) : Prop :=  ((e.map (fun (a,b) => b * f a)).sum = 0)
/-
lemma f_comp : ((fun x ↦match x with
          | (a, b) => ↑b * f a) ∘
        fun x ↦
        match x with
        | (a, b) => (a, q * b)) =
-/
-- theorem sum
theorem sumZero_mul {f: α → ℝ} {e : List (α × ℚ)} (h : sumZero f e1) (q:ℚ) : sumZero f (e.map (fun (a,b) => (a,q*b))) := by
  unfold sumZero
  rw [List.map_map]
  List.sum_map_mul_left
  have
  simp

theorem sumZero_append {f: α → ℝ} {e1 e2 : List (α ×ℚ)} (h1 : sumZero f e1) (h2 :sumZero f e2) : sumZero f (e1 ++ e2) := by
  unfold sumZero at *
  simp only [map_append, sum_append, and_imp]
  simp_all only [add_zero]

theorem sumZero_sort: sumZero f
-- variable (e1 e2 : List (α × ℚ))

-- variable (eqns : ∀ e ∈ ll, ((e.fst).map (fun (a,b) => b * f a)).sum = 0)
-- variable (eqns : ∀ e ∈ ll, toProp f (e.fst))

def all_vars : List α := dedup ((flatMap Prod.fst ll ).map Prod.fst) -- .map(Prod.fst).dedup

-- def get_vars :

variable (v : List (α × ℚ))
def evalAt (eq : List (α × ℚ)) (v : α) : ℚ := (eq.map (fun (x,y) => y*(if x=v then 1 else 0))).sum


variable (thm_all : ∀ v ∈ all_vars ll,
  ∀ e ∈ ll,
    e.snd * (((e.fst).map (fun (x,y) => (y:ℚ)*(if x=v then (1:ℚ) else (0:ℚ)))).sum:ℚ) = 0)
