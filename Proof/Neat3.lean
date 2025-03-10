import Mathlib
open Set
open OrderHom hiding id

macro "R2" : term => `(ℝ × ℝ)
--def R2 := ℝ × ℝ

open AffineMap
open Matrix
open Prod

#check const

-- noncomputable def d0a : R2 →ᵃ[ℝ] R2 := (AffineMap.const _ _ (0,0)) + (LinearMap.toAffineMap <| Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![1, 2 ; 3, (4 :ℝ) ])

#check (!![0.5, -0.5 ; 0.5, 0.5 ] : Matrix (Fin 2) (Fin 2) ℝ )
#check finTwoArrowEquiv
-- noncomputable def MatToAff {n : ℕ} (m : Matrix (Fin n) (Fin (n+1)) ℝ ) : ℕ  := 3

--@[simp]
noncomputable def matToAff (mat : Matrix (Fin 2) (Fin 3) ℝ ) : R2 →ᵃ[ℝ] R2 :=
  (LinearMap.toAffineMap <|
    Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _)
      (submatrix mat id (Fin.castLE (Nat.le_succ 2))))
  + (AffineMap.const ℝ R2 ((finTwoArrowEquiv _).toFun (fun i => mat i 2)))
noncomputable def d0 : R2 →ᵃ[ℝ] R2 := matToAff !![0.5, -0.5, 0 ; 0.5, 0.5, 1]

/- Easier to construct them as affine maps than prove affineness?
@[simp]
def d0 (p : R2) := ((p.1 - p.2) * (0.5 : ℚ ) , (p.1 + p.2) * 0.5 + 1 )

@[simp]
def d1 (p : R2) := ((p.1 + p.2 + 1) * 0.5 , (p.2 - p.1 + 3) * 0.5)
-/

#check !![0.5, -0.5, 0 ; 0.5, 0.5, 0]

--def d0_simp (p : ℝ × ℝ) : ℝ × ℝ  := ((p.1 - p.2) * (0.5 : ℚ ) , (p.1 + p.2) * 0.5 + 1 )
@[simp ]
theorem d0_simp {p : R2 } : d0 p = ((p.1 - p.2) * 0.5 , (p.1 + p.2) * 0.5 + 1 ) := by
  unfold d0
  simp
  constructor <;> ring

noncomputable def d1 : R2 →ᵃ[ℝ] R2 := (LinearMap.toAffineMap <| Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![0.5, 0.5 ; -0.5, 0.5 ])
  + (AffineMap.const _ _ (0.5,1.5))
@[simp ]
theorem d1_simp {p : R2 } : d1 p =  ((p.1 + p.2) * 0.5 + 0.5, (p.2 - p.1) * 0.5 + 1.5) := by
  unfold d1
  simp
  norm_num
  constructor <;> ring

def d0_lin1 := Matrix.toLin' !![1, 2 ; 3, 4 ]
def d0_lin2 := Matrix.mulVecLin !![1, 2 ; 3, 4 ]
--def d0_lin3 := Matrix.toLinearMap₂ !![1, 2 ; 3, 4 ]
--def d0_lin : ℝ × ℝ  →ₗ[ℝ] ℝ × ℝ := Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![1, 2 ; 3, 4 ]


example : d0 (-1,1) = (-1,1) := by
  rw [Prod.eq_iff_fst_eq_snd_eq]
  --apply (Iff.mpr Prod.eq_iff_fst_eq_snd_eq)
  apply And.intro
  unfold d0
  norm_num
  unfold d0
  simp

example : d1 (2,1) = (2,1) := by
  rw [Prod.eq_iff_fst_eq_snd_eq]
  apply And.intro
  . unfold d1
    norm_num
  . unfold d1
    norm_num

def unit_sq : Set R2 := {⟨ x , y ⟩ | 0<x ∧ x<1 ∧ 0<y ∧ y<1 }

def treeFun (s : Set R2) : Set R2 := d0 '' s ∪ d1 '' s ∪ unit_sq

theorem treeFun_monotone : Monotone (treeFun) :=  Monotone.sup (Monotone.sup monotone_image monotone_image) monotone_const

def treeFun_m : Set R2 →o Set R2 := ⟨treeFun, treeFun_monotone⟩

def pythagTree := lfp treeFun_m

theorem sq_in_pyt :  unit_sq ⊆ pythagTree := by
  unfold pythagTree
  rw [← map_lfp treeFun_m]
  exact (le_sup_right)

def pythag_rect : Set R2 := {⟨ x , y ⟩ | -3<x ∧ x<4 ∧ 0<y ∧ y<4 }

variable [CompleteLattice α] [CompleteLattice β] (f : α →o α)

open fixedPoints

theorem lfp_f_eq_lfp_ff : lfp f = lfp (f.comp f) := by
  unfold lfp
  apply le_antisymm
  .
    simp
    intro b h
    have lem : f (b ⊓ f b ) ≤ b ⊓ f b := by
      apply le_inf
      --rel [f.mono,inf_le_right]
      --rel [_]
      transitivity f (f b)
      have k := @inf_le_right
      mono
      --rel [f.mono , @inf_le_right α _ b (f b) ]
      --apply f.mono
      --exact @inf_le_right α _ b (f b)
      trivial
      apply f.mono
      exact inf_le_left
    transitivity (b ⊓ f b)
    transitivity f (b ⊓ f b )
    apply sInf_le
    rw [mem_setOf_eq]
    apply f.mono
    exact lem
    exact lem
    exact inf_le_left
  .
    simp
    intro b h
    have : (f (f b)) ≤ b := by
      apply (le_trans _ h)
      exact (f.mono  h)
    apply sInf_le
    trivial
open Real


open Lean.Parser.Tactic
open Lean
/-
instance : Coe (TSyntax ``locationHyp) (TSyntax `ident) where
  coe s := match s.raw with
    | (Syntax.node info `Lean.Parser.Tactic.locationHyp
                  #[(Syntax.node info2 `null #[t]
                    --(Syntax.ident info "i".toSubstring' (addMacroScope mainModule `i scp) [])
                      ),
                  (Syntax.node info3 `null #[])])  => ⟨ t ⟩
    | _ => ⟨s⟩
-/

macro "norm_bound" : tactic => `(tactic| (norm_num ; bound))


instance : Coe (TSyntax `ident) (TSyntax ``locationHyp) where
  coe s := ⟨ (mkNode `Lean.Parser.Tactic.locationHyp
                  #[(mkNode `null #[s.raw] ),
                  (mkNode `null #[])])   ⟩

macro "rw_pair" i:(ident) : tactic =>
    `(tactic| (
      try (simp at $i ; apply Prod.eq_iff_fst_eq_snd_eq.mp at $i)
      try apply eq_iff_fst_eq_snd_eq.mp at $i
      try simp at $i
      rw [← ($i).left, ← ($i).right]
      ))
macro "rw_pair2" i:(ident) : tactic =>
    `(tactic| (
        simp at $i
        apply Prod.eq_iff_fst_eq_snd_eq.mp at $i
      --  try apply eq_iff_fst_eq_snd_eq.mp at $i
        simp at $i
        rw [← ($i).left, ← ($i).right]
      ))

theorem pyt_in_rect : pythagTree ⊆ pythag_rect := by
  unfold pythagTree
  rw [lfp_f_eq_lfp_ff]
  apply (@lfp_induction _ _ (treeFun_m.comp treeFun_m) (fun x => x ⊆ pythag_rect))
  . intro a h _ ⟨x,y⟩ ht
    unfold pythag_rect
    simp
    cases' ht with q q
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      rw_pair rr
      cases' q with q q
      cases' q with q q <;>
        (
        obtain ⟨ ⟨x,y ⟩ ,⟨q,rr⟩ ⟩ := q
        rw_pair rr
        apply h at q
        unfold pythag_rect at q
        simp at q
        norm_bound
        )
      unfold unit_sq at q
      simp at q
      norm_bound
      )
    unfold unit_sq at q
    simp at q
    bound
  intro s
  exact sSup_le

theorem pyt_area : MeasureTheory.volume pythagTree =
 12823413011547414368862997525616691741041579688920794331363953564934456759066858494476606822552437442098640979
  / 877512406035620068631903180662851572553488753575243048137500508983979170248733422547196905684808937723408093
 := by
  sorry


def pythag_rect2 : Set R2 := {⟨ x , y ⟩ | -2.5<x ∧ x<3.5 ∧ 0<y ∧ y<4 }

theorem pyt_in_rect2 : pythagTree ⊆ pythag_rect2 := by
  unfold pythagTree
  rw [lfp_f_eq_lfp_ff]
  apply (@lfp_induction _ _ (treeFun_m.comp treeFun_m) (fun x => x ⊆ pythag_rect2))
  . intro a h _ ⟨x,y⟩ ht
    unfold pythag_rect2
    norm_num
    --simp
    cases' ht with q q
    cases' q with q q <;>
      (
      cases' q with pt q
      obtain ⟨w,z⟩ := pt
      obtain ⟨q,rr⟩ := q
      rw_pair rr
      cases' q with q q
      cases' q with q q <;>
        (
        obtain ⟨ ⟨x,y ⟩ ,⟨q,rr⟩ ⟩ := q
        rw_pair rr
        apply h at q
        unfold pythag_rect2 at q
        simp at q
        norm_num at q
        norm_bound
        )
      unfold unit_sq at q
      simp at q
      norm_bound
      )
    unfold unit_sq at q
    simp at q
    bound
  intro s
  exact sSup_le

/-
def Cor : Set (R2 →ᵃ[ℝ] R2) := {
  (LinearMap.toAffineMap <| Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _)
        !![0.5, 0 ; 0, 0.5 ])
     + (AffineMap.const _ _ p)
  | (p ∈ ({(0,0),(0.5,0),(0,0.5),(0.5,0.5)} : Set R2))
}

def Rot : Set (R2 →ᵃ[ℝ] R2) := {
  (AffineMap.const ℝ R2  (-0.5,-0.5))
    ∘ (LinearMap.toAffineMap <| Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _)
        !![p.1, p.2 ; -p.2, p.1 ])
    ∘ (AffineMap.const ℝ R2 (0.5,0.5))
  | (p ∈ ({(1,0),(0,1),(-1,0),(0,-1)} : Set R2))
}


noncomputable def Rotl : List (R2 →ᵃ[ℝ] R2) := List.map (fun p =>
  --(AffineMap.const ℝ R2  (-0.5,-0.5))
    (LinearMap.toAffineMap <| Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _)
        !![p.1, p.2 ; -p.2, p.1 ]))
    --(AffineMap.const ℝ R2 (0.5,0.5)))

   ([(1,0),(0,1),(-1,0),(0,-1)] : List R2)

macro "Z2" : term => `(ℤ  × ℤ)
-- Function from squares in 7x4 grid to sets of rotated squares from the grid
def pieces (s : Z2) (cor : Cor) : List (Z2 × Rot) := sorry
-/
#check ℤ
inductive Cor : Type where
  | bl : Cor
  | br : Cor
  | tl : Cor
  | tr : Cor

-- Tranformation (scale and translate) sending unit_sq to a corner of unitsq
noncomputable def corTransform (cor : Cor) : (R2 →ᵃ[ℝ] R2) := match cor with
  | Cor.bl => LinearMap.toAffineMap ((0.5 : ℝ ) • LinearMap.id)
  | Cor.br => LinearMap.toAffineMap ((0.5 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (0.5,0))
  | Cor.tl => LinearMap.toAffineMap ((0.5 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (0,0.5))
  | Cor.tr => LinearMap.toAffineMap ((0.5 : ℝ ) • LinearMap.id)
                + (AffineMap.const ℝ R2 (0.5,0.5))

theorem vol_quater {x: Set R2} {cor : Cor} : MeasureTheory.volume x = MeasureTheory.volume (corTransform cor '' x) / 4 := sorry

theorem corners_disj : Pairwise (Disjoint on (λ c:Cor => corTransform c '' unit_sq ) ) := sorry

inductive Rot : Type where
  | none : Rot
  | left : Rot
  | half : Rot
  | right : Rot

def rcor (r : Rot) (c : Cor) : Cor :=
  sorry


#check ( ( (-0.5,-0.5) +ᵥ .)  : (R2 →ᵃ[ℝ] R2))

-- Tranformation (rotate about (0.5,0.5)) sending unit_sq to unitsq
noncomputable def rotTransform (rot : Rot) : (R2 →ᵃ[ℝ] R2) := match rot with
  | Rot.none => AffineMap.id ℝ R2 --LinearMap.toAffineMap (LinearMap.id)
  | Rot.left => AffineMap.comp (AffineMap.const ℝ R2 (0.5,0.5))
                <| AffineMap.comp (LinearMap.toAffineMap (
                     Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![0, -1 ; 1, 0 ] ))
                ( . +ᵥ (-0.5,-0.5))
  | Rot.half => AffineMap.comp (AffineMap.const ℝ R2 ((0.5 : ℝ) ,(0.5 : ℝ) ))
                <| AffineMap.comp
                  (LinearMap.toAffineMap ((-1 : ℝ ) • LinearMap.id))
                  (AffineMap.const ℝ R2 ((-0.5 : ℝ) ,(-0.5 : ℝ) ))
  | Rot.right => AffineMap.comp (AffineMap.const ℝ R2 (0.5,0.5))
                <| AffineMap.comp (LinearMap.toAffineMap (
                     Matrix.toLin (Basis.finTwoProd _) (Basis.finTwoProd _) !![0, 1 ; -1, 0 ] ))
                (AffineMap.const ℝ R2 (-0.5,-0.5))

theorem thm_rot {rot:Rot}: rotTransform rot '' unit_sq = unit_sq := by
  unfold rotTransform

  cases' rot <;> (
    simp

  )
  sorry


theorem rcor_consistent {rot : Rot} {cor : Cor} : rotTransform rot '' (corTransform cor '' unit_sq) = corTransform (rcor rot cor) '' unit_sq := by sorry

example : (Nat × Nat) = (ℕ × ℕ)  := by
  exact (Eq.refl _)

macro "Z2" : term => `(ℤ × ℤ)

inductive Piece : Type
  | treePiece : Z2 → Rot → Piece
  | trianglePiece : Rot → Piece -- default triangle is
  | emptyPiece : Piece
  | fullPiece : Piece

def pieces (s : Z2) (cor : Cor) : List (Piece) := sorry

def triangleMap (cor) → List Piece :=

def pieceMap (p : Piece) (cor : Cor) : List (Piece) := match piece with
  | treePiece p r =>
  | Triangle
  | emptyPiece => emptyPiece
  | fullPiece => fullPiece

--open SetCoe
theorem piecesMakePythagTree : ∀ s : Z2, ∀ cor : Cor,
  pythagTree ∩ (AffineMap.const ℝ R2 ((s.1 : ℝ) , (s.2 : ℝ) ) '' (cor.1 '' unitsq)) =
  {} -- pieces s cor
 := sorry
