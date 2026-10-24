import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.IntroductionToFunctionalAnalysis.code.OpenMapping
open Function
open OpenMapping

/--
[open_mapping_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/OpenMapping.lean)
-/
@[path]
lemma open_mapping_theorem
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [CompleteSpace V]
  [NormedAddCommGroup W]
  [NormedSpace 𝕜 W]
  [CompleteSpace W]
  {T : V →L[𝕜] W}
-- given
  (hT : Surjective T) :
-- imply
  IsOpenMap T :=
-- proof
  T.isOpenMap hT

/--
[bijective_bounded_inverse](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/OpenMapping.lean)
-/
@[path]
lemma bijective_bounded_inverse
  [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup V]
  [NormedSpace 𝕜 V]
  [CompleteSpace V]
  [NormedAddCommGroup W]
  [NormedSpace 𝕜 W]
  [CompleteSpace W]
  {T : V →L[𝕜] W}
-- given
  (hT : Bijective T) :
-- imply
  ∃ S : W →L[𝕜] V, (∀ w, T (S w) = w) ∧ (∀ v, S (T v) = v) := by
-- proof
  let e := continuousLinearEquivOfBijective T hT
  exact ⟨e.symm.toContinuousLinearMap,
    fun w => e.apply_symm_apply w,
    fun v => e.symm_apply_apply v⟩


-- created on 2026-10-23
-- updated on 2026-10-24
