module

public import Mathlib

public section

/--
[bounded_operators_completeSpace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/BoundedOperators.lean)
-/
public theorem bounded_operators_completeSpace
  {𝕜 : Type*}
  {V W : Type*}
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [NormedAddCommGroup W]
  [NormedSpace 𝕜 W]
  [CompleteSpace W] :
-- imply
  CompleteSpace (V →L[𝕜] W) :=
-- proof
  inferInstance


-- created on 2026-10-23
-- updated on 2026-10-26
