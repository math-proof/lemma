import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_3_3
open LowerUnsignedLebesgueIntegral


/--
[LowerUnsignedLebesgueIntegral.eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_3_3.lean)
-/
@[path]
private lemma main
  {d:ℕ}
  {f: EuclideanSpace' d → EReal}
-- given
  (hf : ∀ x, 0 ≤ f x) :
-- imply
  LowerUnsignedLebesgueIntegral f =
    sSup { R | ∃ g: EuclideanSpace' d → EReal, ∃ hg: UnsignedSimpleFunction g, (AlmostAlways (fun x ↦ g x ≤ f x)) ∧ R = hg.integ} :=
-- proof
  LowerUnsignedLebesgueIntegral.eq hf


-- created on 2026-10-22
