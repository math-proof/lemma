import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.GenusConstruction.Part2
open RiemannRochCurves CanonicalSheafCurves CohomologyP1 RiemannRoch GenusConstruction


namespace GenusConstruction

/--
[chi_P1_struct_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma chi_P1_struct_from_cech
  {k : Type}
  [Field k] :
-- imply
  (dimH0 k 0 : ℤ) - (dimH1 k 0 : ℤ) = 1 := by
-- proof
  have h := riemann_roch_P1 k 0
  linarith

end GenusConstruction

namespace GenusConstruction

/--
[chi_P1_canonical_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma chi_P1_canonical_from_cech
  {k : Type}
  [Field k] :
-- imply
  (dimH0 k (-2) : ℤ) - (dimH1 k (-2) : ℤ) = -1 := by
-- proof
  have h := riemann_roch_P1 k (-2)
  linarith

end GenusConstruction

namespace GenusConstruction

/--
[chi_P1_struct_eq_rrHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma chi_P1_struct_eq_rrHom
  {k : Type}
  [Field k] :
-- imply
  (dimH0 k 0 : ℤ) - (dimH1 k 0 : ℤ) = rrHom 0 (1, 0) := by
-- proof
  rw [rr_value_structure_sheaf]
  exact chi_P1_struct_from_cech k

end GenusConstruction

namespace GenusConstruction

/--
[chi_P1_canonical_eq_rrHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma chi_P1_canonical_eq_rrHom
  {k : Type}
  [Field k] :
-- imply
  (dimH0 k (-2) : ℤ) - (dimH1 k (-2) : ℤ) = rrHom 0 (1, -2) := by
-- proof
  rw [rrHom_apply]
  exact chi_P1_canonical_from_cech k

end GenusConstruction

namespace GenusConstruction

/--
[P1CurveFromCech_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1CurveFromCech_genus
  {k : Type}
  [Field k] :
-- imply
  (P1CurveFromCech k).g = 0 :=
-- proof
  rfl

end GenusConstruction

namespace GenusConstruction

/--
[P1CurveFromCech_eq_mkCurve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1CurveFromCech_eq_mkCurve
  {k : Type}
  [Field k] :
-- imply
  P1CurveFromCech k = mkCurve 0 := by
-- proof
  show P1CurveFromCech k = mkCurve 0
  unfold P1CurveFromCech mkCurve
  congr 1

end GenusConstruction

namespace GenusConstruction

/--
[P1_chi_struct_validated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1_chi_struct_validated
  {k : Type}
  [Field k] :
-- imply
  (P1CurveFromCech k).χ (1, 0) = (dimH0 k 0 : ℤ) - (dimH1 k 0 : ℤ) := by
-- proof
  rw [chi_P1_struct_from_cech k]
  exact (P1CurveFromCech k).hχ_struct

end GenusConstruction

namespace GenusConstruction

/--
[P1_chi_canonical_validated](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1_chi_canonical_validated
  {k : Type}
  [Field k] :
-- imply
  (P1CurveFromCech k).χ (1, (P1CurveFromCech k).degK) = (dimH0 k (-2) : ℤ) - (dimH1 k (-2) : ℤ) := by
-- proof
  rw [chi_P1_canonical_from_cech k]
  exact (P1CurveFromCech k).hχ_canonical

end GenusConstruction

namespace GenusConstruction

/--
[P1_H0_struct_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1_H0_struct_from_cech
  {k : Type}
  [Field k] :
-- imply
  dimH0 k 0 = 1 := by
-- proof
  have := dimH0_nonneg k 0
  simpa using this

end GenusConstruction

namespace GenusConstruction

/--
[P1_H1_struct_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1_H1_struct_from_cech
  {k : Type}
  [Field k] :
-- imply
  dimH1 k 0 = 0 := by
-- proof
  have := dimH1_nonneg k 0
  simpa using this

end GenusConstruction

namespace GenusConstruction

/--
[P1_H0_canonical_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1_H0_canonical_from_cech
  {k : Type}
  [Field k] :
-- imply
  dimH0 k (-2) = 0 :=
-- proof
  canonical_bundle_P1_H0 k

end GenusConstruction

namespace GenusConstruction

/--
[P1_H1_canonical_from_cech](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma P1_H1_canonical_from_cech
  {k : Type}
  [Field k] :
-- imply
  dimH1 k (-2) = 1 :=
-- proof
  canonical_bundle_P1_H1 k

end GenusConstruction

namespace GenusConstruction

/--
[curveFromDedekind_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma curveFromDedekind_genus
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  (curveFromDedekind k A).g = curveGenus k A :=
-- proof
  rfl

end GenusConstruction

namespace GenusConstruction

/--
[curveFromDedekind_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma curveFromDedekind_degK
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  (curveFromDedekind k A).degK = 2 * (curveGenus k A : ℤ) - 2 :=
-- proof
  rfl

end GenusConstruction

namespace GenusConstruction

/--
[curveFromDedekind_eq_mkCurve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma curveFromDedekind_eq_mkCurve
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  curveFromDedekind k A = mkCurve (curveGenus k A) := by
-- proof
  simp only [curveFromDedekind, mkCurve]

end GenusConstruction

namespace GenusConstruction

/--
[curveFromDedekind_eq_toSmoothCompleteCurve](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma curveFromDedekind_eq_toSmoothCompleteCurve
  [Field k]
  {C : DedekindCurve k} :
-- imply
  curveFromDedekind k C.A = C.toSmoothCompleteCurve := by
-- proof
  have hchi : C.cohChi = rrHom (C.ddGenus : ℤ) :=
    additive_homs_eq_of_generators_eq C.cohChi (rrHom (C.ddGenus : ℤ))
      (by rw [C.cohChi_struct_eq, rr_value_structure_sheaf])
      (by rw [C.cohChi_sky_eq, rr_value_skyscraper])
  simp only [curveFromDedekind, DedekindCurve.toSmoothCompleteCurve,
    DedekindCurve.ddGenus, DedekindCurve.degK, curveGenus]
  congr 1
  exact hchi.symm

end GenusConstruction

namespace GenusConstruction

/--
[ddGenus_eq_curveFromDedekind_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma ddGenus_eq_curveFromDedekind_genus
  [Field k]
  {C : DedekindCurve k} :
-- imply
  (C.ddGenus : ℤ) = (curveFromDedekind k C.A).g := by
-- proof
  simp [curveFromDedekind, DedekindCurve.ddGenus, curveGenus]

end GenusConstruction

namespace GenusConstruction

/--
[curveFromDedekind_degK_eq_dedekind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
lemma curveFromDedekind_degK_eq_dedekind
  [Field k]
  {C : DedekindCurve k} :
-- imply
  (curveFromDedekind k C.A).degK = C.toSmoothCompleteCurve.degK := by
-- proof
  rw [curveFromDedekind_eq_toSmoothCompleteCurve]
end GenusConstruction


/--
[P1CurveFromCech_degK](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/GenusConstruction.lean)
-/
@[path]
private lemma P1CurveFromCech_degK_eq
  {k : Type}
  [Field k] :
-- imply
  (P1CurveFromCech k).degK = -2 := by
-- proof
  apply GenusConstruction.P1CurveFromCech_degK k


-- created on 2026-10-23
