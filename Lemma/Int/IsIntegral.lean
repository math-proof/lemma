import Mathlib
import sympy.Basic
import Instance.v1.Atlas.LieGroups.code.HilbertNoether


/--
[hilbert_noether_integral](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HilbertNoether.lean)
-/
@[path]
private lemma hilbert_noether_integral
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [Group G]
  [Finite G]
  [MulSemiringAction G A]
  [SMulCommClass G R A] :
-- imply
  Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
-- proof
  Algebra.IsInvariant.isIntegral _ A G

/--
[hilbert_noether_module_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HilbertNoether.lean)
-/
@[path]
private lemma hilbert_noether_module_finite
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [Group G]
  [Finite G]
  [MulSemiringAction G A]
  [SMulCommClass G R A]
  [Algebra.FiniteType R A] :
-- imply
  Module.Finite (FixedPoints.subalgebra R A G) A := by
-- proof
  have : Algebra.IsIntegral (FixedPoints.subalgebra R A G) A :=
    hilbert_noether_integral (R := R) (A := A) (G := G)
  have : Algebra.FiniteType (FixedPoints.subalgebra R A G) A :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (FixedPoints.subalgebra R A G) A
  exact Algebra.IsIntegral.finite

/--
[hilbert_noether_fg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/HilbertNoether.lean)
-/
@[path]
private lemma hilbert_noether_fg
  [CommRing R]
  [CommRing A]
  [Algebra R A]
  [Group G]
  [Finite G]
  [MulSemiringAction G A]
  [SMulCommClass G R A]
  [IsNoetherianRing R]
  [Algebra.FiniteType R A] :
-- imply
  Algebra.FiniteType R (FixedPoints.subalgebra R A G) :=
-- proof
  ⟨fg_of_fg_of_fg R (↥(FixedPoints.subalgebra R A G)) A
    (Algebra.FiniteType.out (R := R) (A := A))
    (hilbert_noether_module_finite (R := R) (A := A) (G := G)).1
    Subtype.val_injective⟩


-- created on 2026-10-23
-- updated on 2026-10-24
