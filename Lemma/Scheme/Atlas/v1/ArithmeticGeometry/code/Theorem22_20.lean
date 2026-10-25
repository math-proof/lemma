import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.Theorem22_20
open Theorem22_20
open RiemannRochSpace CurveWithOrd


namespace Theorem22_20

/--
[lemma_22_13_curve_level](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Theorem22_20.lean)
-/
@[path]
lemma lemma_22_13_curve_level
  [AddCommGroup Ω]
  [Module F Ω]
  [Module k Ω]
  [IsScalarTower k F Ω]
  {divΩ : Ω → CurveDivisor C}
  {D : CurveDivisor C}
-- given
  (h_add : ∀ ω₁ ω₂ : Ω, ω₁ + ω₂ ≠ 0 → ∀ P, min ((divΩ ω₁) P) ((divΩ ω₂) P) ≤ (divΩ (ω₁ + ω₂)) P)
  (h_smul : ∀ (c : k) (ω : Ω), c • ω ≠ 0 → ∀ P, (divΩ ω) P ≤ (divΩ (c • ω)) P) :
-- imply
  (Module.finrank k (differentialSpaceD (k := k) divΩ D h_add h_smul) : ℤ) = indexOfSpeciality (F := F) (k := k) D :=
-- proof
  dim_differentialSpaceD_eq_indexOfSpeciality divΩ D h_add h_smul

end Theorem22_20


-- created on 2026-10-23
