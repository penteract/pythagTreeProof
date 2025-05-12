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
