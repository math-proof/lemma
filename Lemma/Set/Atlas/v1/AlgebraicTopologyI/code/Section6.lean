import Mathlib
import sympy.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
open Finset BigOperators AlgebraicTopologyI


/--
[faceMap_mem_stdSimplex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section6.lean)
-/
@[path]
private lemma faceMap_mem_stdSimplex_eq
  {n : ℕ}
  {i : Fin (n + 2)}
  {t : Fin (n + 1) → ℝ}
-- given
  (ht : t ∈ stdSimplex ℝ (Fin (n + 1))) :
-- imply
  Fin.insertNth i (0 : ℝ) t ∈ stdSimplex ℝ (Fin (n + 2)) := by
-- proof
  apply AlgebraicTopologyI.faceMap_mem_stdSimplex n i t ht


-- created on 2026-10-23
