import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ChevalleyFiberDimension
open PrimeSpectrum Topology ChevalleyFiberDim


namespace ChevalleyFiberDim

/--
[fiberKrullDim_generic_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma fiberKrullDim_generic_eq
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsDomain B]
  [Algebra B A] :
-- imply
  fiberKrullDim (A := A) (genericPoint B) = ringKrullDim A := by
-- proof
  unfold fiberKrullDim genericPoint
  exact RingEquiv.ringKrullDim
    ((Ideal.quotEquivOfEq (Ideal.map_bot (f := algebraMap B A))).trans
      (RingEquiv.quotientBot A))

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[fiber_nontrivial_of_in_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma fiber_nontrivial_of_in_image
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  {q : PrimeSpectrum B}
-- given
  (hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B A))) :
-- imply
  Nontrivial (A ⧸ (q.asIdeal.map (algebraMap B A))) := by
-- proof
  obtain ⟨p, hp⟩ := hq
  have hle : q.asIdeal.map (algebraMap B A) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    show b ∈ (PrimeSpectrum.comap (algebraMap B A) p).asIdeal
    rw [hp]; exact hb
  have : Nontrivial (A ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top p.isPrime)
  exact (Ideal.Quotient.factor_surjective hle).nontrivial

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[fiber_dim_usc_image_constructible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma fiber_dim_usc_image_constructible
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A] :
-- imply
  IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) :=
-- proof
  isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp ‹_›))

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[fiberKrullDim_anti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma fiberKrullDim_anti
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  {q q' : PrimeSpectrum B}
-- given
  (hle : q.asIdeal ≤ q'.asIdeal) :
-- imply
  fiberKrullDim (A := A) q' ≤ fiberKrullDim (A := A) q :=
-- proof
  ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (Ideal.map_mono hle))
    (Ideal.Quotient.factor_surjective (Ideal.map_mono hle))

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[fiberKrullDim_le_generic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma fiberKrullDim_le_generic
  [CommRing B]
  [CommRing A]
  [IsDomain B]
  [Algebra B A]
  {q : PrimeSpectrum B} :
-- imply
  fiberKrullDim (A := A) q ≤ fiberKrullDim (A := A) (genericPoint B) :=
-- proof
  fiberKrullDim_anti bot_le

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[Lemma33Data.fiber_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma Lemma33Data.fiber_nontrivial
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  {L : Lemma33Data B A}
  {q : PrimeSpectrum B}
-- given
  (hq : q ∈ (↑(basicOpen L.b) : Set (PrimeSpectrum B))) :
-- imply
  Nontrivial (A ⧸ (q.asIdeal.map (algebraMap B A))) :=
-- proof
  fiber_nontrivial_of_in_image (L.basicOpen_sub_image hq)

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[Lemma33Data.fiberKrullDim_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma Lemma33Data.fiberKrullDim_nonneg
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  {L : Lemma33Data B A}
  {q : PrimeSpectrum B}
-- given
  (hq : q ∈ (↑(basicOpen L.b) : Set (PrimeSpectrum B))) :
-- imply
  (0 : WithBot ℕ∞) ≤ fiberKrullDim (A := A) q :=
-- proof
  @ringKrullDim_nonneg_of_nontrivial _ _ (L.fiber_nontrivial hq)

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[fiberDimGeInImage_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma fiberDimGeInImage_eq_inter
  [CommRing B]
  [CommRing A]
  [Algebra B A]
  {d : ℕ} :
-- imply
  fiberDimGeInImage (A := A) d = Set.range (PrimeSpectrum.comap (algebraMap B A)) ∩ fiberDimGe (A := A) (d : WithBot ℕ∞) := by
-- proof
  ext q
  simp [fiberDimGeInImage, fiberDimGe, Set.mem_inter_iff, Set.mem_setOf_eq]

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[flat_morphism_isOpenMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma flat_morphism_isOpenMap
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A]
  [Module.Flat B A] :
-- imply
  IsOpenMap (PrimeSpectrum.comap (algebraMap B A)) := by
-- proof
  have : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  exact isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end ChevalleyFiberDim

namespace ChevalleyFiberDim

/--
[chevalley_thm21_2_part1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean)
-/
@[path]
lemma chevalley_thm21_2_part1
  {B A : Type*}
  [CommRing B]
  [CommRing A]
  [IsNoetherianRing B]
  [Algebra B A]
  [Algebra.FiniteType B A] :
-- imply
  IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) :=
-- proof
  fiber_dim_usc_image_constructible B A
/-- The locus where the fiber dimension is at least `d` is closed: this is the geometric form of
upper semicontinuity of fiber dimension. -/

end ChevalleyFiberDim


-- created on 2026-10-23
