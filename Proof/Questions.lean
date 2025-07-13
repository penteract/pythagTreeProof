import Mathlib
-- Why is this not computable?
noncomputable def d0_lin : ℝ × ℝ  →ₗ[ℝ] ℝ × ℝ := Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![1, 2 ; 3, 4 ]


-- Why is % defined uselessly on ℝ?

-- #check Module.finrank
#check Module.finrank

instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) where
  out := by rw [finrank_euclideanSpace, Fintype.card_fin]

noncomputable section

macro "R2" : term => `(ℝ × ℝ)

lemma fnrnk : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  rw [finrank_euclideanSpace, Fintype.card_fin]
/-
instance : Fact (FiniteDimensional.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n) where
  out := by rw [finrank_euclideanSpace, Fintype.card_fin]

instance : Fact (FiniteDimensional.finrank ℝ ((Fin (↑(1+1))) → ℝ) = 2) where
  out := by

    rewrite [← (@fnrnk 2)]
    rewrite [(@fnrnk 2)]
    nth_rewrite 0 [(@fnrnk 2)]
    nth_rewrite 1 [← (@fnrnk 2).out]
    apply LinearEquiv.finrank_eq
    symm
    exact (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv
-/
instance : Fact (Module.finrank ℝ (ℝ × ℝ) = 2) where
  out := by
    rw [← @fnrnk 2]
    apply LinearEquiv.finrank_eq
    symm
    exact LinearEquiv.trans (EuclideanSpace.equiv (Fin 2) ℝ).toLinearEquiv (LinearEquiv.finTwoArrow ℝ ℝ )


#check (Orientation.rightAngleRotation _ : R2 ≃ₗᵢ[ℝ] R2)
/-
@LinearIsometryEquiv ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (RingHom.id ℝ) ⋯ ⋯ (ℝ × ℝ) (ℝ × ℝ)
  NormedAddCommGroup.toSeminormedAddCommGroup NormedAddCommGroup.toSeminormedAddCommGroup NormedSpace.toModule
  NormedSpace.toModule : Type
@LinearIsometryEquiv ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (RingHom.id ℝ) ⋯ ⋯ (ℝ × ℝ) (ℝ × ℝ)
  Prod.seminormedAddCommGroup Prod.seminormedAddCommGroup Prod.instModule Prod.instModule
-/


#check (@Orientation.rightAngleRotation  _ : (Fin 2 → ℝ) ≃ₗᵢ[ℝ] (Fin 2 → ℝ))
/-
 @LinearIsometryEquiv ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (RingHom.id ℝ) ⋯ ⋯ (Fin 2 → ℝ) (Fin 2 → ℝ)
    NormedAddCommGroup.toSeminormedAddCommGroup NormedAddCommGroup.toSeminormedAddCommGroup NormedSpace.toModule
    NormedSpace.toModule : Type
but is expected to have type
  @LinearIsometryEquiv ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ) (RingHom.id ℝ) ⋯ ⋯ (Fin 2 → ℝ) (Fin 2 → ℝ)
    Pi.seminormedAddCommGroup Pi.seminormedAddCommGroup (Pi.Function.module (Fin 2) ℝ ℝ)
    (Pi.Function.module (Fin 2) ℝ ℝ) : TypeLean 4
    -/


open Real

def rot_neg_pi_div_4 (o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)) :
    (EuclideanSpace ℝ (Fin 2)) ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin 2)) :=
  o.rotation (.coe (-(π/4)))


lemma fnrnk' : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := by
  rw [finrank_euclideanSpace, Fintype.card_fin]

instance : Fact (Module.finrank ℝ ((Fin (↑(1+1))) → ℝ) = 2) where
  out := by
    -- rw succeeds, nth_rw fails???
    --rewrite [← (@fnrnk 2)]
    nth_rewrite 0 [← (@fnrnk' 2)]
    sorry


--def d0_lin2 : ℕ  × ℕ  →ₗ[ℕ] ℕ × ℕ := Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![1, 2 ; 3, 4 ]

-- Should I be using (ℝ × ℝ) or ((Fin 2) → ℝ )?

-- is there a form of const_mono that proves const x is monotone?

-- why does apply le_antisymm with a goal of A =ᶠ[ae volume] ⋃ i, t i (f i)
--  give volume {x | (fun x ↦ A x = iUnion (fun i ↦ t i (f i)) x) x}ᶜ ≤ 0
--  despite
--   "Although Set is defined as α → Prop, this is an implementation detail which should not be relied on"


-- why do some of the following fail
variable (A B : Set α)
theorem t (s: A ⊆ B) (f : Set α → Set α) :
    f (B ∩ A) = f A := by
      -- works1:
      -- rw [Set.inter_eq_self_of_subset_right s]

      -- Fail 1
      -- rw [inf_of_le_right s]
      -- Fail 2 (what does erw do differently from rw?)
      -- erw [inf_of_le_right s]
      -- Fail 3
      --let a  := (inf_of_le_right s)
      --rw [a]
      -- works 2
      let a : B ∩ A = A := (inf_of_le_right s)
      rw [a]

theorem rw_under_quantifier {x:ℝ }: ∃ y : ℝ, x<0 ∧ (2⁻¹ * x=y) ∨ (2⁻¹ * y=x) := by
    have h {a b:ℝ }:2⁻¹ * a = b ↔ a = 2*b := by norm_num; bound
    rw [(by norm_num;bound : (q:ℝ) →  2⁻¹ * q  = q/2)]
    -- Why can't it rewrite
    --rw [(by norm_num;bound : (q:ℝ) →  2⁻¹ * q  = q/2)]
    -- answer: use simp
    simp [(by norm_num;bound : (q:ℝ) →  2⁻¹ * q  = q/2)]
    erw [(sorry : (q:ℝ) →  2⁻¹ * q  = q/2)]
    erw [h]

-- no coercion from pairs to pairs

theorem tt {A : Set ℝ} {ι : Type*} {i : ι} {s : Set ι} {S : Set ℝ} {t : ι → Set ℝ → Set ℝ}:
  MeasureTheory.volume (A ∩ ((⋃ x ∈ s, t x S) \ (⋃ x ∈ (Singleton.singleton i), t x S))) =
  MeasureTheory.volume (A ∩ (⋃ x ∈ (s \ {i}), t x S)) := by

  rw [biUnion_diff_biUnion_eq (s:=s) (t:={i}) (f:=(fun j => t j S))]

-- What is the difference between:
--  variable {iotaFinite : Fintype ι}
--  variable [Countable ι]
def unit_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 }
def cor_sq : Set (ℝ × ℝ) := {⟨ x , y ⟩ | 0<x ∧ x<0.5 ∧ 0<y ∧ y<0.5 }

inductive Cor : Type where
  | bl : Cor
  | br : Cor
  | tl : Cor
  | tr : Cor
  deriving DecidableEq

instance Cor.fintype : Fintype Cor := ⟨ ⟨ {bl,br,tl,tr}, by simp⟩ , fun x => by cases x <;> simp⟩

theorem R2Caratheodory {s : Set (ℝ×ℝ) } {t : Set (ℝ×ℝ) } (h : MeasurableSet s) :
    MeasureTheory.volume s = MeasureTheory.volume (t ∩ s) + MeasureTheory.volume (t \ s) := by
  sorry


open Real
open AffineMap
open Matrix
open Prod
-- macro "R2" : term => `(ℝ × ℝ)
-- Tranformation (scale and translate) sending unit_sq to a corner of unitsq
noncomputable def corTransform (cor : Cor) : (R2 →ᵃ[ℝ] R2) := match cor with
  | Cor.bl => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
  | Cor.br => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (1/2,0))
  | Cor.tl => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (0,1/2))
  | Cor.tr => LinearMap.toAffineMap ((1/2 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (1/2,1/2))

lemma cor : cor_sq = corTransform Cor.bl '' unit_sq := by
  ext ⟨ x,y⟩
  have h : ⇑(corTransform Cor.bl) = (fun (p : (ℝ × ℝ)) => (p.1*0.5, p.2*0.5)) := by
    ext ⟨a,b⟩ <;> (
      simp [corTransform]
      norm_num
      bound)
  rw [h]
  unfold cor_sq
  simp [unit_sq,cor_sq]
  norm_num

  bound

-- induction on finite sets
--lemma lem_fin {ι : Type*} [Finite ι] (p : Set ι → Prop) (ih : ∀ (s: Set ι), ∀x : ι, (x∉s) → p s → p (insert x a))  : s ⊆ := by
  --sorry
  -- Set.Finite.induction_to_univ

-- openClassical
noncomputable def notunivchoice (nottop : A≠Set.univ) : α := by
  --exact Classical.choice (Set.nonempty_compl.mpr nottop)
  exact Set.Nonempty.some (Set.nonempty_compl.mpr nottop)




lemma l (n : Nat) (a b : Fin n): a + b ≡ (a + b : Fin n) [ZMOD n] := by
  rw [Lean.Omega.Fin.ofNat_val_add]
  rw [Int.ModEq.eq_1]
  symm
  exact Int.emod_emod_of_dvd _ (dvd_refl _)

def tstl1 : List (ℤ ) :=
  let (z,x)  := ((3:ℤ), (3 : ℤ) )
  List.flatMap
   (fun ⟨ tp,r⟩ => let ⟨x,y⟩  := tp + (3,0) -- ( tp + (3:ℤ),tp)
    [cond r x y].concat (if r then 9 else 8))
    [((z+1,x+1),true)]
def tstl2 : List (ℤ ) :=
  let (z,x)  := ((3:ℤ), (3 : ℤ) )
  List.flatMap
   (fun ⟨ tp,r⟩ => let ⟨x,y⟩  := tp + (3,0) -- ( tp + (3:ℤ),tp)
    if r then [cond r x y] else [cond r x y])
    [((z+1,x+1),true)]

def tstl3 (z : ℤ ) : List (ℤ ×ℤ ) :=
  let (z,x)  := ((3:ℤ), (3 : ℤ) )
  List.flatMap
   (fun ⟨ tp,r⟩ => let ⟨x,y⟩  := tp + (3,0)
    cond r [tp + (3,0)] [])
    [((z+1,x+1),true)]

def triangle : Set (ℝ×ℝ) := {⟨x,y⟩  | 0<x ∧ true}
def triangle2 : Set (ℝ×ℝ) := {⟨x,y⟩  | x>0 ∧ true}


-- why isn't something like this solved by simp?
lemma add_mess {a b c d e f g : ℝ } :
 a +
    (b +
      (c +
        (d +
          (e + (f + g))))) =
  g +
    (f +
      (d +
        (c + (e
          + (a + b)))))
        := by
        --aesop
        sorry


lemma lem {x : ℝ }  (h : 5 / 2 < 2 + x) : 1<2*x := by
  -- bound
  linarith

lemma l2 {x : ℝ } : 5 / 2 < 2 + x ↔ 1<2*x:= by
  apply Iff.intro <;> (intros; linarith)

lemma lem2 {x y : ℝ } :
  ((3 < x - y + 4 ∧ x < y) ∧ 0 < y + x ∧ y + x < 1) ∧ (0 < x ∧ 4 + x < 4.5) ∧ 3 / 2 < 1 + y ∧ 1 + y < 2 ↔
  0 < x ∧ 1 < 2 * y ∧ 2 * x + (2 * y - 1) < 1 := by
  apply Iff.intro
  intro h
  and_intros
  bound
  linarith
  bound
  bound



theorem thm (x : ℕ ) (h : x>0) :
   7 = (match x with
         | 5 => 8
         | 0 => 2
         | n => 3):= by
  sorry




lemma lemq {x y:ℝ}: (∃ a b, ((3 < a ∧ a < 4) ∧ 0 < b ∧ b < 1) ∧ (a + b + 4) * 0.5 = 4 + x ∧ (b - a + 6) * 0.5 = 1 + y) ∧
    (0 < x ∧ 4 + x < 4.5) ∧ 3 / 2 < 1 + y ∧ 1 + y < 2 ↔
      ∃ a b, (0 < a ∧ 0 < b ∧ a + b < 1) ∧ 2⁻¹ * a = x ∧ 2⁻¹ * b + 2⁻¹ = y
  := by
    have h (a b : ℝ) :(a + b + 4) * 0.5 = 4 + x ∧ (b - a + 6) * 0.5 = 1 + y
      ↔ a = (x-y) + 4 ∧ b = y + x
    := by
      bound
    have h' (a b : ℝ ) : 2⁻¹ * a  = x ∧ 2⁻¹ * b+ 2⁻¹ = y ↔ a = 2*x ∧ b = 2*y - 1 := by
      bound
    simp [h,h']
    apply Iff.intro <;>
      (intro
       and_intros <;> linarith)

open Set
lemma lem3 : (fun x ↦ (4, 1) + x) ⁻¹' ((fun a ↦ ((a.1 + a.2 + 4) * 0.5, (a.2 - a.1 + 6) * 0.5)) '' Ioo 3 4 ×ˢ Ioo 0 1) ∩
    (fun x ↦ (4, 1) + x) ⁻¹' Ioo (4:ℝ) (4.5:ℝ) ×ˢ Ioo (3 / 2 :ℝ ) (2:ℝ) =
  (fun (a:ℝ×ℝ ) ↦ (2:ℝ)⁻¹ • a + (0, 2⁻¹)) '' {(x, y) | 0 < x ∧ 0 < y ∧ x + y < 1}
   := by
   ext ⟨x,y⟩
   simp
   exact lemq

def corPos (xn : Fin 7) (yn : Fin 4) (cor : Cor) : ℤ × ℤ  := match cor with
  | .bl => (2*xn,2*yn)
  | .tl => (2*xn,2*yn+1)
  | .tr => (2*xn+1,2*yn+1)
  | .br => (2*xn+1,2*yn)

def corPos' (cor : Cor) : ℤ × ℤ  := match cor with
  | .bl => (2,2)
  | .tl => (2,2+1)
  | .tr => (2+1,2+1)
  | .br => (2+1,2)

theorem second_gen_squares
  (cor : Cor)
  (hh : cor= cor)
  : (∅ : Set R2) =
      Multiset.sup (List.map (fun (x:Set R2) => x)
            (match cor with
              | Cor.bl => [∅]
              | Cor.tl => [triangle]
              | Cor.tr => [∅]
              | Cor.br => [∅])) := by
  sorry
theorem second_gen_squares'
  (cor : Cor)

  : ( cor= cor) → (∅ : Set R2) =
      Multiset.sup (List.map (fun (x:Set R2) => x)
            (match cor with
              | Cor.bl => [∅]
              | Cor.tl => [triangle]
              | Cor.tr => [∅]
              | Cor.br => [∅])) := by
  intro h
  exact (second_gen_squares cor h)
  sorry

inductive Test : Type where
  | test1 : Test
  | test2 : Test
  deriving DecidableEq

theorem match_test
  (t : Test) (h:t=t)
  : (0:ℕ) =
            (match t with
              | Test.test1 => 0
              | Test.test2 => 0 ) := by
  sorry
theorem match_test'
  (t : Test)
  : t=t → (0:ℕ) =
            (match t with
              | Test.test1 => 0
              | Test.test2 => 0 ) := by
  intro h
  --exact (match_test t h)
  sorry

def f (x:ℝ) : Set R2 := sorry
lemma ll : f hd ⊔ (f tl) ∩ ⇑(corTransform c) '' usq =
    f hd ∪ (f tl) ∩ ⇑(corTransform c) '' usq := by
    -- exact (sup_eq_union _ _)
    -- rw [Set.sup_eq_union]
    sorry


inductive Piece : Type
  | treePiece : Fin 7 → Fin 4 → ZMod 4 → Piece
  | trianglePiece : ZMod 4 → Piece -- (triangle none) is bottom left half of unit_sq
  | emptyPiece : Piece
  | fullPiece : Piece
  deriving DecidableEq,Ord



-- Why does Multiset.sup_dedup need [DecidableEq α]?
--   Why does Multiset.dedup need [DecidableEq α]?
--     Why does Multiset.dedup need to be computable


-- what is the difference between `decide` and  `with_unfolding_all decide`?

-- Why are sums so painful to work with?
   -- It won't
   -- !!very important solution: Finset.sum_coe_sort
#check Finset.sum_toList
variable (s : Finset α )
-- lemma Finset_sum_nonsense (∑ x : s, )

theorem prod_extend_by_one {M ι} {k:M}  [CommMonoid M] [DecidableEq ι] (s : Finset ι) (f : ι → M) :
    ∏ i ∈ s, (if i ∈ s then f i else k) = ∏ i ∈ s, f i :=
  (Finset.prod_congr rfl) fun _i hi => if_pos hi


-- How to use loogle:
-- 1) there's a theorem you know is true, suspect is in mathlib and you want to find it (or something close enough to it)
-- search for the most general true form of the theorem you want (e.g AffineMap rather than LinearMap or AffineIsometryEquiv)
-- leave quite a few underscores in, try various orders with commuting operators (including equality)
-- 2) You want to prove something not too tricky (i.e. you wouldn't usually bother writing a proof out in paper)
--    but have no idea what mathlib might provide to help you
-- Do a search for the types and operations you're working with
-- Look through the pages at https://leanprover-community.github.io for the types you care about,
--  keeping an eye out for typeclass instances and stuff your types could be coerced/converted into.
-- Also, use simp? to find the theorems mathlib thinks you should definitely know about

-- When should I try split a proof up?
-- A: More often than I currently do

-- How often is it easier to
