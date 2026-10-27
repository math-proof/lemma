import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzSingularSupport
open MeasureTheory Set ConeSupport


/--
[schwartz_singularSupport_empty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzSingularSupport.lean)
-/
@[path]
private lemma schwartz_singularSupport_empty_eq
  {n : ℕ}
  {f : 𝓢(E n, ℂ)} :
-- imply
  singularSupport (schwEmbed f) = ∅ := by
-- proof
  apply ConeSupport.schwartz_singularSupport_empty f


-- created on 2026-10-23
