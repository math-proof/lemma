import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Euclidean.ErdosAnning
open MetaMathlibExt


/--
[erdos_anning](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Euclidean/ErdosAnning.lean)
-/
@[path]
private lemma erdos_anning_eq
  :
-- imply
  ∀ (S : Set (EuclideanSpace ℝ (Fin 2))), S.Infinite →
    (∀ p ∈ S, ∀ q ∈ S, ∃ n : ℕ, dist p q = (n : ℝ)) → Collinear ℝ S := by
-- proof
  apply MetaMathlibExt.erdos_anning


-- created on 2026-10-20
