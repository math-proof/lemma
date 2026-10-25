import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
open StatMech StatMech.FrontierD


/--
[exists_eq_of_intUnitSteps_between](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegerUnitStepPlateau.lean)
-/
@[path]
private lemma exists_eq_of_intUnitSteps_between_eq
  {f : Nat → Int}
  {a b : Nat}
  {r : Int}
-- given
  (hstep : IntUnitSteps f)
  (hab : a ≤ b)
  (har : f a ≤ r)
  (hrb : r ≤ f b) :
-- imply
  ∃ n, a ≤ n ∧ n ≤ b ∧ f n = r := by
-- proof
  apply StatMech.FrontierD.exists_eq_of_intUnitSteps_between hstep hab har hrb

/--
[exists_intUnitStep_bracketedPlateau](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/IntegerUnitStepPlateau.lean)
-/
@[path]
private lemma exists_intUnitStep_bracketedPlateau_eq
  {f : Nat → Int}
  {N : Nat}
  {r : Int}
-- given
  (hstep : IntUnitSteps f)
  (hzero : f 0 = 0)
  (hr : 0 < r)
  (hreach : r + 1 ≤ f N) :
-- imply
  ∃ a b : Nat, 0 < a ∧ a ≤ b ∧ b < N ∧ f (a - 1) = r - 1 ∧ (∀ n, a ≤ n → n ≤ b → f n = r) ∧ (∀ n < b + 1, f n < r + 1) ∧ f (b + 1) = r + 1 := by
-- proof
  apply StatMech.FrontierD.exists_intUnitStep_bracketedPlateau hstep hzero hr hreach


-- created on 2026-10-23
