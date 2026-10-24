import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.Symp2TangentSpaces
open DifferentialFormSpace SymplecticLinearAlgebra


/--
[symp2StdJ_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Symp2TangentSpaces.lean)
-/
@[path]
private lemma symp2StdJ_sq_eq
  {X : Symp2VF} :
-- imply
  symp2StdJ (symp2StdJ X) = (-X.1, -X.2) := by
-- proof
  apply symp2StdJ_sq X

/--
[symp2_iota_neg_components](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Symp2TangentSpaces.lean)
-/
@[path]
private lemma symp2_iota_neg_components_eq
  {a b : Poly2}
  {α : Symp2Ω 1} :
-- imply
  symp2Iota (-a, -b) α = -symp2Iota (a, b) α := by
-- proof
  apply symp2_iota_neg_components a b α

/--
[symp2_lift_sq_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Symp2TangentSpaces.lean)
-/
@[path]
private lemma symp2_lift_sq_neg_eq
  {X : Symp2VF}
  {α : Symp2Ω 1} :
-- imply
  symp2DFS.ι (symp2StdJ (symp2StdJ X)) α = -(symp2DFS.ι X α) := by
-- proof
  apply symp2_lift_sq_neg X α

/--
[symp2_lift_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Symp2TangentSpaces.lean)
-/
@[path]
private lemma symp2_lift_preserves_eq
  {u v : Symp2VF}
  {ω : Symp2Ω 2} :
-- imply
  symp2DFS.ι (symp2StdJ u) (symp2DFS.ι (symp2StdJ v) ω) = symp2DFS.ι u (symp2DFS.ι v ω) := by
-- proof
  apply symp2_lift_preserves u v ω

/--
[symp2_lift_taming](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Symp2TangentSpaces.lean)
-/
@[path]
private lemma symp2_lift_taming_eq
  {S : SymplecticManifold Symp2Ω Symp2VF} :
-- imply
  Function.Injective (fun (v : Symp2VF) => symp2DFS.ι (symp2StdJ v) S.ω) := by
-- proof
  apply symp2_lift_taming S


-- created on 2026-10-23
