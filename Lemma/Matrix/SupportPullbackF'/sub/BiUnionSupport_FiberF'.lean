import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.DivisorPushPull
open AlgebraicCurve AlgebraicCurve.Divisor


/-- ported from external source -/
@[path]
private lemma main
  [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [DecidableEq (Place K F')]
  {E : Divisor K F} :
-- imply
  (Divisor.pullback F' E).support ⊆ E.support.biUnion (fun v => v.fiber F') := by
-- proof
  classical
    intro w hw
    exact Finset.mem_biUnion.mpr ⟨w.restrict F,
      restrict_mem_support_of_mem_support_pullback hw, w.restrict_mem_fiber⟩


-- created on 2026-10-23
