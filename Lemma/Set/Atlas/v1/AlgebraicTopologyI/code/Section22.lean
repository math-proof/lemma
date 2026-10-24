import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section22
open FundamentalHomologicalAlgebra


/--
[lift_commutes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section22.lean)
-/
@[path]
private lemma lift_commutes_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Y Z : C}
  {f : Y ⟶ Z}
  {P : ProjectiveResolution Y}
  {Q : FundamentalThm.Resolution Z} :
-- imply
  lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
-- proof
  apply FundamentalHomologicalAlgebra.lift_commutes f P Q


-- created on 2026-10-23
