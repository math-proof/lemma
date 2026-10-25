import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology.Part4
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace ZariskiSheafCohomology


namespace ZariskiSheafCohomology

/--
[subsingleton_cohomology_of_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiSheafCohomology.lean)
-/
@[path]
lemma subsingleton_cohomology_of_isZero
  {X : Scheme}
  {F : Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat}
  {n : ℕ}
-- given
  (h : Limits.IsZero F) :
-- imply
  Subsingleton (F.H n) :=
-- proof
  Sheaf.subsingleton_H_of_isZero h n

end ZariskiSheafCohomology


-- created on 2026-10-23
