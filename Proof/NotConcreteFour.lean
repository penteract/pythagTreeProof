import Mathlib
import Proof.Eqns
import Proof.CertProof


noncomputable def vol := MeasureTheory.volume ∘ getTiles

theorem volFin {ps : List Piece} : vol ps ≠ ⊤ := by
  apply (ne_top_of_lt (b:=⊤))
  simp only [vol, Function.comp_apply]
  apply LE.le.trans_lt (MeasureTheory.measure_mono getTiles_in_usq)
  rw [vol_usq]
  exact ENNReal.one_lt_top

noncomputable def vol' (ps: List Piece) : ℝ  := ENNReal.toReal (vol ps)

theorem vol_cors (ps : List Piece) : vol ps =
    vol (canon_cor_rot Cor.tl ps) / 4 +
    vol (canon_cor_rot Cor.br ps) / 4 +
    vol (canon_cor_rot Cor.bl ps) / 4 +
    vol (canon_cor_rot Cor.tr ps) / 4 := by
    rw [vol,Function.comp_apply]
    nth_rw 1 [vol_corners_sorted]
    simp only [Function.comp_apply]
    ring -- rearrange things due to the version I used to generate allparts

theorem vol_cors' (ps : List Piece) : vol' ps =
    vol' (canon_cor_rot Cor.tl ps) / 4 +
    vol' (canon_cor_rot Cor.br ps) / 4 +
    vol' (canon_cor_rot Cor.bl ps) / 4 +
    vol' (canon_cor_rot Cor.tr ps) / 4 := by
  have h:= @volFin ps
  simp_all only [vol_cors ps, vol']
  -- #check ENNReal.add_ne_top.mp h
  have ⟨h4',h4⟩ := (ENNReal.add_ne_top.mp h)
  have ⟨h3',h3⟩ := ENNReal.add_ne_top.mp h4'
  have ⟨ h1,h2⟩:= ENNReal.add_ne_top.mp h3'
  rw [← ENNReal.toReal_ofNat 4]
  simp only [← ENNReal.toReal_div]
  let tst := ENNReal.toReal_add h1 h2
  rw [← ENNReal.toReal_add h1 h2,
      ← ENNReal.toReal_add h3' h3,
      ← ENNReal.toReal_add h4' h4]

theorem vol_cors'' (ps : List Piece) : 4 * vol' ps =
    List.sum (List.map (fun cor => vol' (canon_cor_rot cor ps)) [Cor.tl, Cor.br, Cor.bl, Cor.tr]) := by
  rw [vol_cors']
  simp
  ring

theorem vol_full' : vol' [Piece.fullPiece] = 1 := by
  simp [getTiles,getTile,vol_usq,vol,vol']

theorem vol_empty' : vol' [] = 0 := by
  simp [getTiles,getTile,vol,vol']


-- theorem bigMat_is_system1 : bigMat
theorem fromAllParts_pyt_eqns {a b q} (h : (a,b,q) ∈ allparts) : Eqns.fromAllParts (a,b,q) ∈ pyt_eqns.toFinset := by
  unfold pyt_eqns Eqns.fromAllParts
  simp_all only [List.mem_toFinset, List.mem_map, Prod.mk.injEq, List.cons.injEq, and_true, Prod.exists,
    exists_eq_right_right]
  apply Exists.intro
  · apply Exists.intro
    · apply And.intro
      · exact h
      · apply And.intro
        · simp_all only
        · rfl

/-
def pyt_eqns_to_part ( e : pyt_eqns.toFinset) : List Piece × List (List Piece) × ℚ := by
  obtain ⟨x,xin ⟩ := e
  simp [pyt_eqns] at xin
  obtain ⟨a,b⟩ := xin -/

def cors := [Cor.tl, Cor.br, Cor.bl, Cor.tr]

theorem expand_mat {a b q} (h : (a,b,q) ∈ allparts) {hh}:
    bigMat (Subtype.mk (Eqns.fromAllParts (a,b,q)) hh /-(fromAllParts_pyt_eqns h)-/) x
    = (if a = ↑x then 4 else 0) + (List.map (fun y ↦ if canon_cor_rot y a = ↑x then -1 else 0) cors).sum
     := by
  unfold bigMat
  unfold pyt_eqns
  unfold Eqns.getMat
  simp only [Matrix.of_apply]
  unfold Eqns.fromAllParts
  simp only [List.map_cons, List.map_map, List.sum_cons]
  conv_lhs =>
    rhs
    rhs
    lhs
    ext y
    simp
  have ap := allParts_describes_pyt _ h
  simp only at ap
  rw [ap]
  rw [List.map_map]
  simp only [List.map_cons, List.map_nil] at ap
  rw [← cors]
  rfl

-- theorem redef_bigMat : bigMat = Matrix.of (fun f )


-- bigMat eqn x = ()
lemma a_in_allvars (h : (a, b, q) ∈ allparts) : a∈ Eqns.all_vars pyt_eqns := by
  unfold Eqns.all_vars
  simp only [List.mem_dedup, List.mem_map, List.mem_flatMap, Prod.exists, exists_and_right,
    exists_eq_right]
  unfold pyt_eqns
  simp only [List.mem_map, Prod.mk.injEq, Prod.exists, exists_eq_right_right]
  use 4
  apply Exists.intro
  apply And.intro
  use q
  use a
  use b
  exact List.mem_cons_self
def aps := allparts


lemma stuff_in_allvars (h : (a, b, q) ∈ allparts) : canon_cor_rot cor a ∈  Eqns.all_vars pyt_eqns := by
  unfold Eqns.all_vars
  simp only [List.mem_dedup, List.mem_map, List.mem_flatMap, Prod.exists, exists_and_right,
    exists_eq_right]
  unfold pyt_eqns
  simp only [List.mem_map, Prod.mk.injEq, Prod.exists, exists_eq_right_right]
  use -1
  use ((a, 4) :: List.map (fun x ↦ (x, -1)) b)
  apply And.intro
  use q
  use a
  use b
  apply List.mem_cons_of_mem
  have h : canon_cor_rot cor a ∈ b := by
    have hh := allParts_describes_pyt _ h
    simp only at hh
    rw [hh]
    apply List.mem_map_of_mem
    fin_cases cor <;> trivial
  simp_all only [List.mem_map, Prod.mk.injEq, and_true, exists_eq_right]

theorem subtype_eq {s : Finset ι} {a:ι} (b : s) (h :a∈ s) : a = b ↔ Subtype.mk a h = b := by
  rw [← Subtype.val_inj]


#check ∑ x, x
-- @Finset.sum ?m.8312 ?m.8312 ?m.8310 Finset.univ fun x ↦ x : ?m.8312

#check ∑ x∈ Finset.univ, x
-- @Finset.sum ?m.11450 ?m.11450 ?m.11452 ?m.11455 fun x ↦ x : ?m.11450

theorem finset_list_sum [AddCommMonoid r] [Fintype s] (f : s → β → r)
   : ∑ x ∈ s',  List.sum (List.map (f x) l) = List.sum (List.map (fun y => ∑ x∈ s', f x y) l) := by
  induction l with
  | nil => simp
  | cons h t ih=>
    simp only [List.map_cons, List.sum_cons]
    rw [Finset.sum_add_distrib]
    simp_all

-- ∑ x, vol' ↑x * (List.map (Rat.cast ∘ fun y ↦ if canon_cor_rot y a = ↑x then -1 else 0) cors).sum



-- set_option maxRecDepth 200
theorem bigMat_vol_is_system :
    Matrix.mulVec (Matrix.map bigMat ((↑) : ℚ → ℝ ))
    (Subtype.restrict _ vol') = 0 := by
  have ap := allParts_describes_pyt
  simp only [Matrix.mulVec_eq_sum, op_smul_eq_smul]
  ext eqn
  obtain ⟨ e, einmap ⟩ := eqn
  unfold pyt_eqns at einmap
  simp only [List.mem_toFinset, List.mem_map, Prod.exists] at einmap
  obtain ⟨ a,b,q,abqinallparts,edef⟩ := einmap
  simp only [Pi.zero_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul,
    Pi.zero_apply]
  have h : e = Eqns.fromAllParts (a,b,q) := by
    rw [← edef]
    rfl
  simp only [h]
  simp only [expand_mat abqinallparts]
  simp only [Rat.cast_add, Rat.cast_list_sum, List.map_map]
  simp only [Subtype.restrict_apply, apply_ite, Rat.cast_ofNat, Rat.cast_zero]
  simp only [left_distrib, mul_ite, mul_zero]
  -- have hh' := (a_in_allvars' (by sorry : [] ∈ Eqns.all_vars pyt_eqns))

  simp only [subtype_eq _ (List.mem_toFinset.mpr (a_in_allvars abqinallparts))]
  simp only [subtype_eq _ (List.mem_toFinset.mpr (stuff_in_allvars abqinallparts))]
  rw [Finset.univ_eq_attach]
  rw [Finset.sum_add_distrib]
  -- rw [← Finset.univ_eq_attach]
  simp only [← List.sum_map_mul_left]
  simp only [Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte, Function.comp_apply, apply_ite,
    Rat.cast_neg, Rat.cast_one, Rat.cast_zero, mul_neg, mul_one, mul_zero]
  rw [finset_list_sum]
  simp only [Finset.sum_ite_eq, Finset.mem_attach, ↓reduceIte]
  rw [mul_comm]
  rw [vol_cors'' a]
  unfold cors
  simp?
  ring


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


#check RingHom.map_vecMul

theorem allParts_makes_eqn_R :
    Matrix.vecMul (fun e => e.val.snd) (Matrix.map bigMat ((↑) : ℚ → ℝ )) =
    (fun v => Rat.cast (if v.val=[] then -qEmpty else
              if v.val=[Piece.fullPiece] then -qFull else
              if v.val ∈ init then 1 else 0 )) := by
  -- have mvm := RingHom.map_vecMul (Rat.castHom ℝ) bigMat
  ext v
  have ap1 := congrFun (congrArg (Rat.castHom ℝ ∘ · ) allParts_makes_eqn) v
  simp only [Function.comp_apply] at ap1
  conv_lhs at ap1 =>
    rw [RingHom.map_vecMul (Rat.castHom ℝ) bigMat (fun e => e.val.snd) v]
    simp only [Rat.coe_castHom]
    enter [1]
    ext x
    simp only [Function.comp_apply]
  simp only [eq_ratCast] at ap1
  exact ap1

-- theorem bigMat.map

-- theorem nodup_av : Nodup (all_vars es) := by sorry
theorem vol_inits_val : List.sum (List.map vol' init) = qFull * vol' [Piece.fullPiece] + qEmpty * vol' [] := by
  have h := Eqns.mat_z bigMat_vol_is_system allParts_makes_eqn_R
  --TODO!!
  have es2 := es_makes_eqn
  apply congrArg (fun f => ((↑):ℚ→ℝ) ∘ f ) at es2
  rw [funext_iff] at es2
  simp only [Function.comp_apply] at es2
  simp only [mq_cast_r] at es2
  rw [← funext_iff] at es2
  have h := mat_z bigMat_vol_is_system allParts_makes_eqn
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
