import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzContinuity
open SchwartzMap TemperedDistributions
open scoped SchwartzMap


namespace TemperedDistributions

/--
[continuous_of_isBounded_schwartz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzContinuity.lean)
-/
@[path]
lemma continuous_of_isBounded_schwartz
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {T : 𝓢(E, G) →ₗ[ℝ] 𝓢(E, G)}
-- given
  (hbound : Seminorm.IsBounded (schwartzSeminormFamily ℝ E G) (schwartzSeminormFamily ℝ E G) T) :
-- imply
  Continuous T :=
-- proof
  WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms ℝ E G)
    (schwartz_withSeminorms ℝ E G) T hbound

end TemperedDistributions

namespace TemperedDistributions

/--
[isBounded_schwartz_of_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzContinuity.lean)
-/
@[path]
lemma isBounded_schwartz_of_continuous
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {T : 𝓢(E, G) →L[ℝ] 𝓢(E, G)} :
-- imply
  Seminorm.IsBounded (schwartzSeminormFamily ℝ E G) (schwartzSeminormFamily ℝ E G) T.toLinearMap := by
-- proof
  intro i
  have hcont : Continuous ((schwartzSeminormFamily ℝ E G i).comp T.toLinearMap) := by
    show Continuous (fun x => schwartzSeminormFamily ℝ E G i (T x))
    exact ((schwartz_withSeminorms ℝ E G).continuous_seminorm i).comp T.continuous
  obtain ⟨s, C, _, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ E G)
      ((schwartzSeminormFamily ℝ E G i).comp T.toLinearMap) hcont
  exact ⟨s, C, hle⟩

end TemperedDistributions

namespace TemperedDistributions

/--
[continuous_linearMap_schwartz_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzContinuity.lean)
-/
@[path]
lemma continuous_linearMap_schwartz_iff
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup G]
  [NormedSpace ℝ G]
  {T : 𝓢(E, G) →ₗ[ℝ] 𝓢(E, G)} :
-- imply
  Continuous T ↔ Seminorm.IsBounded (schwartzSeminormFamily ℝ E G) (schwartzSeminormFamily ℝ E G) T := by
-- proof
  constructor
  · intro hcont
    exact isBounded_schwartz_of_continuous ⟨T, hcont⟩
  · exact continuous_of_isBounded_schwartz T
end TemperedDistributions



-- created on 2026-10-23
