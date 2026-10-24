import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section12
open CategoryTheory AlgebraicTopology Limits BarycentricSubdivision


namespace BarycentricSubdivision

/--
[barycenter_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section12.lean)
-/
@[path]
lemma barycenter_coord
  {n : ℕ}
  {i : Fin (n + 1)} :
-- imply
  (barycenter n).val i = 1 / (n + 1 : ℝ) :=
-- proof
  rfl

end BarycentricSubdivision

/--
[chainGroup_eq_coprod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section12.lean)
-/
@[path]
private lemma chainGroup_eq_coprod_eq
  {X : TopCat.{0}}
  {n : ℕ} :
-- imply
  (singularChainFunctorZ.obj X).X n = ∐ (fun (_ : SingType X n) => AddCommGrpCat.of ℤ) := by
-- proof
  apply BarycentricSubdivision.chainGroup_eq_coprod X n


-- created on 2026-10-23
