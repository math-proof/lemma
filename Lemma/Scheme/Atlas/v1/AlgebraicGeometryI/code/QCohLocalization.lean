import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.QCohLocalization
open AlgebraicGeometry CategoryTheory QCohLocalization
open LocalizedModule


namespace QCohLocalization

/--
[localization_preserves_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean)
-/
@[path]
lemma localization_preserves_injective
  [CommRing R]
  {S : Submonoid R}
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N}
-- given
  (hf : Function.Injective f) :
-- imply
  Function.Injective (LocalizedModule.map S f) :=
-- proof
  LocalizedModule.map_injective S f hf

end QCohLocalization

namespace QCohLocalization

/--
[localization_preserves_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean)
-/
@[path]
lemma localization_preserves_surjective
  [CommRing R]
  {S : Submonoid R}
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  {f : M →ₗ[R] N}
-- given
  (hf : Function.Surjective f) :
-- imply
  Function.Surjective (LocalizedModule.map S f) :=
-- proof
  LocalizedModule.map_surjective S f hf

end QCohLocalization

namespace QCohLocalization

/--
[localization_exact_middle](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean)
-/
@[path]
lemma localization_exact_middle
  [CommRing R]
  {S : Submonoid R}
  [AddCommGroup M']
  [Module R M']
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup M'']
  [Module R M'']
  {f : M' →ₗ[R] M}
  {g : M →ₗ[R] M''}
-- given
  (hex : Function.Exact f g) :
-- imply
  Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
-- proof
  LocalizedModule.map_exact S f g hex

end QCohLocalization

namespace QCohLocalization

/--
[localization_preserves_exactness](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/QCohLocalization.lean)
-/
@[path]
lemma localization_preserves_exactness
  [CommRing R]
  {S : Submonoid R}
  [AddCommGroup M]
  [Module R M]
  [AddCommGroup N]
  [Module R N]
  [AddCommGroup P]
  [Module R P]
  {f : M →ₗ[R] N}
  {g : N →ₗ[R] P}
-- given
  (hfg : Function.Exact f g) :
-- imply
  Function.Exact (LocalizedModule.map S f) (LocalizedModule.map S g) :=
-- proof
  LocalizedModule.map_exact S f g hfg
end QCohLocalization
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u



-- created on 2026-10-23
