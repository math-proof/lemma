import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.PrincipalIdele
open NumberField.TopologicalIdeleGroup


/--
[principalIdeles_discrete](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/PrincipalIdele.lean)
-/
@[path]
private lemma principalIdeles_discrete_eq
  [Field K] [NumberField K] :
-- imply
  DiscreteTopology (principalIdeles (𝓞 K) K) := by
-- proof
  apply NumberField.TopologicalIdeleGroup.principalIdeles_discrete K


-- created on 2026-10-20
