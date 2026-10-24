import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_Divisor_evalFun_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_add.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F]
  {f : F}
  {D E : Divisor K F}
-- given
  (hD : ∀ v ∈ D.support, Place.evalAt v f ≠ 0)
  (hE : ∀ v ∈ E.support, Place.evalAt v f ≠ 0) :
-- imply
  Divisor.evalFun f (D + E) = Divisor.evalFun f D * Divisor.evalFun f E := by
-- proof
  classical
    refine Finsupp.prod_add_index (fun v _ => zpow_zero _) (fun v hv b₁ b₂ => ?_)
    refine zpow_add₀ ?_ b₁ b₂
    rcases Finset.mem_union.mp hv with h | h
    · exact hD v h
    · exact hE v h


-- created on 2026-10-23
