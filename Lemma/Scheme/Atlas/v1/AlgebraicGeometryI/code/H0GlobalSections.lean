import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.H0GlobalSections
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace ZariskiSheafCohomology DedekindCurve
open ZariskiSheafCohomology


/--
[finrank_self_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean)
-/
@[path]
lemma finrank_self_eq_one
  {k : Type*}
  [Field k] :
-- imply
  Module.finrank k k = 1 :=
-- proof
  Module.finrank_self k
namespace DedekindCurve
variable {k : Type*} [Field k]

namespace DedekindCurve

/--
[h0_O_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean)
-/
@[path]
lemma h0_O_eq_one
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.h0_O = 1 :=
-- proof
  rfl

end DedekindCurve

namespace DedekindCurve

/--
[eulerCharO_from_h0_h1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean)
-/
@[path]
lemma eulerCharO_from_h0_h1
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.eulerCharO = (C.h0_O : ℤ) - (h1_O k C.A : ℤ) := by
-- proof
  simp only [eulerCharO, h0_O, h1_O_eq_genus, ddGenus, Nat.cast_one]

end DedekindCurve

namespace DedekindCurve

/--
[cohChi_struct_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean)
-/
@[path]
lemma cohChi_struct_decomp
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.cohChi (1, 0) = (C.h0_O : ℤ) - (h1_O k C.A : ℤ) := by
-- proof
  rw [cohChi_struct, h0_O, Nat.cast_one]

end DedekindCurve

namespace DedekindCurve

/--
[h0_plus_h1_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean)
-/
@[path]
lemma h0_plus_h1_eq
  [Field k]
  {C : DedekindCurve k} :
-- imply
  (C.h0_O : ℤ) + (h1_O k C.A : ℤ) = 1 + (C.ddGenus : ℤ) := by
-- proof
  simp [h0_O, h1_O_eq_genus, ddGenus]

end DedekindCurve

namespace DedekindCurve

/--
[eulerCharO_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/H0GlobalSections.lean)
-/
@[path]
lemma eulerCharO_consistent
  [Field k]
  {C : DedekindCurve k} :
-- imply
  C.eulerCharO = (C.h0_O : ℤ) - (C.ddGenus : ℤ) := by
-- proof
  simp [eulerCharO, h0_O, ddGenus, Nat.cast_one]
end DedekindCurve
end



-- created on 2026-10-23
