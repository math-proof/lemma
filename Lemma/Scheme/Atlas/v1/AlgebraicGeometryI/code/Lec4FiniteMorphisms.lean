import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Lec4FiniteMorphisms
open AlgebraicGeometry PrimeSpectrum TopologicalSpace Set Lec4


namespace Lec4

/--
[finiteMorphism_closedMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4FiniteMorphisms.lean)
-/
@[path]
lemma finiteMorphism_closedMap
  {X Y : Scheme}
  {f : X ⟶ Y}
  [IsFinite f] :
-- imply
  IsClosedMap f :=
-- proof
  f.isClosedMap

end Lec4

namespace Lec4

/--
[finiteMorphism_finitePreimage](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4FiniteMorphisms.lean)
-/
@[path]
lemma finiteMorphism_finitePreimage
  {X Y : Scheme}
  {f : X ⟶ Y}
  [IsFinite f]
  {y : Y} :
-- imply
  (f ⁻¹' {y}).Finite :=
-- proof
  f.finite_preimage_singleton y

end Lec4

namespace Lec4

/--
[comap_surjective_of_finite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4FiniteMorphisms.lean)
-/
@[path]
lemma comap_surjective_of_finite_injective
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
-- given
  (hinj : Function.Injective (algebraMap B A)) :
-- imply
  Function.Surjective (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  have hInt : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  exact (algebraMap_isIntegral_iff.mpr hInt).comap_surjective hinj

end Lec4

namespace Lec4

/--
[comap_finite_fibers_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4FiniteMorphisms.lean)
-/
@[path]
lemma comap_finite_fibers_of_finite
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
  {p : PrimeSpectrum B} :
-- imply
  (PrimeSpectrum.comap (algebraMap B A) ⁻¹' {p}).Finite :=
-- proof
  Algebra.QuasiFinite.finite_comap_preimage_singleton p

end Lec4

namespace Lec4

/--
[comap_lt_comap_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec4FiniteMorphisms.lean)
-/
@[path]
lemma comap_lt_comap_of_finite
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  [Module.Finite B A]
  {I J : Ideal A}
  [I.IsPrime]
-- given
  (hIJ : I < J) :
-- imply
  Ideal.comap (algebraMap B A) I < Ideal.comap (algebraMap B A) J := by
-- proof
  have hInt : Algebra.IsIntegral B A := Algebra.IsIntegral.of_finite B A
  obtain ⟨x, hxJ, hxI⟩ := Set.exists_of_ssubset hIJ
  exact Ideal.comap_lt_comap_of_integral_mem_sdiff hIJ.le ⟨hxJ, hxI⟩
    (Algebra.IsIntegral.isIntegral x)

end Lec4


-- created on 2026-10-23
