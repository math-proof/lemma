import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SerreDualityDedekind
open nonZeroDivisors SerreDualityDedekind
open scoped TensorProduct


namespace SerreDualityDedekind

/--
[serre_duality_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma serre_duality_ideal
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] (I : Ideal A), h1_ideal k A I = Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k]) :=
-- proof
  fun _ _ _ _ _ _ _ _ _ => rfl

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[h1_ideal_top_eq_h1_O](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma h1_ideal_top_eq_h1_O
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A], h1_ideal k A ⊤ = DedekindCurve.h1_O k A := by
-- proof
  intro k _ A _ _ _ _ _
  simp only [h1_ideal, DedekindCurve.h1_O]
  exact (((LinearEquiv.arrowCongr Submodule.topEquiv
    (LinearEquiv.refl A (Ω[A⁄k]))).restrictScalars k).trans
    (LinearMap.ringLmapEquivSelf A k (Ω[A⁄k]))).finrank_eq

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[finrank_hom_top_eq_finrank_omega](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma finrank_hom_top_eq_finrank_omega
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [Algebra k A] :
-- imply
  Module.finrank k ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) = Module.finrank k (Ω[A⁄k]) :=
-- proof
  (homTopOmegaEquivK k A).finrank_eq

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[serre_duality_structure_sheaf_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma serre_duality_structure_sheaf_consistent
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  DedekindCurve.h1_O k A = Module.finrank k (Ω[A⁄k]) := by
-- proof
  have h1 : h1_ideal k A ⊤ = DedekindCurve.h1_O k A :=
    h1_ideal_top_eq_h1_O k A
  have h2 : h1_ideal k A ⊤ = Module.finrank k ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) :=
    serre_duality_ideal k A ⊤
  have h3 : Module.finrank k ((⊤ : Submodule A A) →ₗ[A] Ω[A⁄k]) =
    Module.finrank k (Ω[A⁄k]) :=
    finrank_hom_top_eq_finrank_omega k A
  linarith

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[h1_ideal_top_eq_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma h1_ideal_top_eq_genus
  {k : Type*}
  [Field k]
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  h1_ideal k A ⊤ = Module.finrank k (Ω[A⁄k]) := by
-- proof
  rw [serre_duality_ideal, finrank_hom_top_eq_finrank_omega]

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[cech_serre_duality_P1_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma cech_serre_duality_P1_nonneg
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : 0 ≤ n) :
-- imply
  Module.finrank k (SheafCohomology.H1 k n) = Module.finrank k (SheafCohomology.H0 k (-2 - n)) :=
-- proof
  SheafCohomology.serre_duality_nonneg k n hn

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[cech_serre_duality_P1_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma cech_serre_duality_P1_neg
  {k : Type}
  [Field k]
  {n : ℤ}
-- given
  (hn : n < 0) :
-- imply
  Module.finrank k (SheafCohomology.H1 k n) = Module.finrank k (SheafCohomology.H0 k (-2 - n)) :=
-- proof
  SheafCohomology.serre_duality_neg k n hn

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[cech_serre_duality_P1_all](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma cech_serre_duality_P1_all
  {k : Type}
  [Field k]
  {n : ℤ} :
-- imply
  Module.finrank k (SheafCohomology.H1 k n) = Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
-- proof
  by_cases hn : 0 ≤ n
  · exact cech_serre_duality_P1_nonneg k n hn
  · push Not at hn
    exact cech_serre_duality_P1_neg k n hn

end SerreDualityDedekind

namespace SerreDualityDedekind

/--
[serre_duality_ideal_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityDedekind.lean)
-/
@[path]
lemma serre_duality_ideal_sheaf
-- imply
  ∀ (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A] [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] (I : Ideal A), h1_ideal_sheaf k A I = Module.finrank k ((I : Submodule A A) →ₗ[A] Ω[A⁄k]) :=
-- proof
  fun _ _ _ _ _ _ _ _ _ => rfl

end SerreDualityDedekind


-- created on 2026-10-23
