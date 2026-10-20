import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.LunnonDimensionDecomposition
open scoped BigOperators
open MetaMathlibExt


/--
[lunnon_fixed_polycube_dimension_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean)
-/
@[path]
private lemma lunnon_fixed_polycube_dimension_decomposition_eq
  {d n : ℕ}
-- given
  (hn : 1 < n) :
-- imply
  fixedPolycubeCount d n =
    Finset.sum (Finset.Ico 1 n) (fun i => Nat.choose d i * properFixedPolycubeCount n i) := by
-- proof
  apply MetaMathlibExt.lunnon_fixed_polycube_dimension_decomposition d n hn


-- created on 2026-10-20
