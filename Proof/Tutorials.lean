import Lean
import Mathlib
open Lean

open Expr

open Nat

def ex31 : Expr :=
  app (app (const ``Nat.add []) (mkNatLit 1)) (mkNatLit 2)

def ex32 : Expr :=
  mkAppN (const ``Nat.add []) #[mkNatLit 1, mkNatLit 2]

def ex33 : Expr :=
  lam `x (const ``Nat []) (mkAppN (const `Nat.add []) #[mkNatLit 1 , Expr.bvar 0 ]) BinderInfo.default

def ex36 : Expr :=
  lam `x (const ``String []) (mkAppN (const ``String.append []) #[mkStrLit "hello, " , Expr.bvar 0 ]) BinderInfo.default

elab "test" : term => return ex36

#check test
#check (fun x => HAdd.hAdd 1 + x)

#eval test "a"
/-
Lean.Expr.app
  (Lean.Expr.app
    (Lean.Expr.app (Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]) (Lean.Expr.const `Nat []))
    (Lean.Expr.lit (Lean.Literal.natVal 3)))
  (Lean.Expr.app (Lean.Expr.const `instOfNatNat []) (Lean.Expr.lit (Lean.Literal.natVal 3)))

-/

#eval mkNatLit (3 : Nat )
#check OfNat.ofNat
#eval ex31
#check (const ``Nat.zero [])
namespace Playground2

-- The scoped modifier makes sure the syntax declarations remain in this `namespace`
-- because we will keep modifying this along the chapter
scoped syntax "⊥" : term -- ⊥ for false
scoped syntax "⊤" : term -- ⊤ for true
scoped syntax:40 term " OR " term : term
scoped syntax:50 term " AND " term : term
#check_failure ⊥ OR (⊤ AND ⊥) -- elaboration function hasn't been implemented but parsing passes

end Playground2

-- Name literals are written with this little ` in front of the name
#eval Syntax.mkApp (mkIdent `Nat.add) #[Syntax.mkNumLit "1", Syntax.mkNumLit "1"] -- is the syntax of `Nat.add 1 1`
#eval mkNode `«term_+_» #[Syntax.mkNumLit "1", mkAtom "+", Syntax.mkNumLit "1"] -- is the syntax for `1 + 1`
#check Lean.ParserDescr

-- note that the `«term_+_» is the auto-generated SyntaxNodeKind for the + syntax

elab "custom_sorry_2" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    Lean.Elab.admitGoal goal

theorem k : 2=3 := by
  sorry

theorem test_custom_sorry (x: 2=3): 1 = 2 := by
  (rw [k] at x ; (sorry)) <;> sorry

open Lean.Parser.Tactic


variable {u:Type}
variable {a b c d : u}

theorem eq_iff_fst_eq_snd_eq : (a,b)=(c,d) ↔ (a=b)∧ c=d := by
  simp

-- 1. We declare the syntax `and_then`
syntax tactic " and_then " locationHyp : tactic

-- 2. We write the expander that expands the tactic
--    into running `a`, and then running `b` on all goals produced by `a`.
macro_rules
| `(tactic| $a:tactic and_then $b:locationHyp) =>
    `(tactic| $a:tactic; simp at $b:locationHyp)

instance : Coe (TSyntax ``locationHyp) (TSyntax `ident) where
  coe s := ⟨s.raw⟩
syntax "rw_pair2" locationHyp : tactic
macro_rules
| `(tactic| rw_pair2 $i) => `(tactic|  apply [eq_iff_fst_eq_snd_eq] at $i)

--macro "rw_pair" i:(locationHyp) : tactic =>
    --`(tactic| simp at $i and_then  rw [Prod.eq_iff_fst_eq_snd_eq] at $i)



macro "rw_pair3" i:(locationHyp) : tactic =>
    `(tactic| (
      try (simp at $i ; apply eq_iff_fst_eq_snd_eq.mpr at $i)
      try apply eq_iff_fst_eq_snd_eq.mpr at $i
      rw [← ($i).left, ← ($i).right]
      ))


theorem t : (a,b) = (c,d) -> a=b := by
  intro h
  rw_pair2 h
  split h
  rw [h.left]
  sorry

syntax "rw_pair2" term : tactic
macro_rules
  | `(tactic| rw_pair2 $p:ident) =>
          `(tactic| simp at $p)
examplt
