import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.ContractibleHomology
open ContractibleHomology


/--
[singularHomology_isZero_of_contractible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ContractibleHomology.lean)
-/
@[path]
private lemma singularHomology_isZero_of_contractible_eq
  {X Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {X : Type}
  [TopologicalSpace X]
  [ContractibleSpace X]
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  IsZero (((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)) := by
-- proof
  apply ContractibleHomology.singularHomology_isZero_of_contractible X n hn


-- created on 2026-10-23
