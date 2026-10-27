import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CohomologyAxiomsElimination
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace ZariskiSheafCohomology CohomologyAxiomsElimination
open ZariskiSheafCohomology


namespace CohomologyAxiomsElimination

/--
[h1_O_defined_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma h1_O_defined_eq_genus
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A] :
-- imply
  h1_O_defined k A = Module.finrank k (Ω[A⁄k]) :=
-- proof
  rfl

end CohomologyAxiomsElimination

namespace CohomologyAxiomsElimination

/--
[h1_O_defined_eq_h1_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma h1_O_defined_eq_h1_O
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  h1_O_defined k A = DedekindCurve.h1_O k A := by
-- proof
  rw [h1_O_defined, DedekindCurve.h1_O_eq_genus]

end CohomologyAxiomsElimination

namespace CohomologyAxiomsElimination

/--
[h1_sky_defined_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma h1_sky_defined_eq_zero
  {k : Type*}
  [Field k]
  {A : Type*} :
-- imply
  h1_sky_defined k A = 0 :=
-- proof
  rfl

end CohomologyAxiomsElimination

namespace CohomologyAxiomsElimination

/--
[h1_sky_defined_eq_h1_sky](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma h1_sky_defined_eq_h1_sky
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  h1_sky_defined k A = DedekindCurve.h1_sky k A := by
-- proof
  rw [h1_sky_defined, DedekindCurve.h1_sky_eq_zero]

end CohomologyAxiomsElimination

namespace CohomologyAxiomsElimination

/--
[groundedCohChi_struct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma groundedCohChi_struct
  [Field k]
  {C : DedekindCurve k} :
-- imply
  groundedCohChi C (1, 0) = 1 - (C.ddGenus : ℤ) := by
-- proof
  simp [groundedCohChi, h1_O_defined, DedekindCurve.ddGenus]

end CohomologyAxiomsElimination

namespace CohomologyAxiomsElimination

/--
[groundedCohChi_sky](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma groundedCohChi_sky
  [Field k]
  {C : DedekindCurve k} :
-- imply
  groundedCohChi C (0, 1) = 1 := by
-- proof
  simp [groundedCohChi, h1_sky_defined]

end CohomologyAxiomsElimination

namespace CohomologyAxiomsElimination

/--
[groundedCohChi_eq_cohChi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean)
-/
@[path]
lemma groundedCohChi_eq_cohChi
  [Field k]
  {C : DedekindCurve k} :
-- imply
  groundedCohChi C = C.cohChi := by
-- proof
  ext ⟨r, d⟩
  simp only [groundedCohChi, DedekindCurve.cohChi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  congr 1

end CohomologyAxiomsElimination


-- created on 2026-10-23
