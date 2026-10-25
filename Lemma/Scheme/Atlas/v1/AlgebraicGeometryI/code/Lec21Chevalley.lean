import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec21Chevalley
open PrimeSpectrum Topology


/--
[fiberDimGeInImage_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec21Chevalley.lean)
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

/--
[chevalley_thm21_2_part1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec21Chevalley.lean)
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
  IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) := by
-- proof
  have hfp : (algebraMap B A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp ‹Algebra.FiniteType B A›)
  exact PrimeSpectrum.isConstructible_range_comap hfp
/-- Upper-semicontinuity of fiber dimension: the locus of points in `Spec B` where the fiber
of a dominant finite-type morphism has dimension at least `d` is closed. -/


-- created on 2026-10-23
