import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.BanachSpace

/--
[goldstine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BanachSpace.lean)
-/
@[path]
private lemma goldstine_eq
-- given
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] :
-- imply
  closure
    ((StrongDual.toWeakDual ∘ NormedSpace.inclusionInDoubleDual 𝕜 E) ''
      Metric.closedBall (0 : E) 1)
    = WeakDual.toStrongDual ⁻¹' Metric.closedBall
      (0 : StrongDual 𝕜 (StrongDual 𝕜 E)) 1 := by
-- proof
  apply FunctionalAnalysis.BanachSpace.goldstine

-- created on 2026-10-10
