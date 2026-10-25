import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.PushforwardExactAffine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits PushforwardExactAffine


namespace PushforwardExactAffine

/--
[restrictScalars_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardExactAffine.lean)
-/
@[path]
lemma restrictScalars_exact
  {R S : Type v}
  [CommRing R]
  [CommRing S]
  {φ : R →+* S} :
-- imply
  PreservesFiniteLimits (ModuleCat.restrictScalars.{v} φ) ∧ PreservesFiniteColimits (ModuleCat.restrictScalars.{v} φ) :=
-- proof
  ⟨inferInstance, inferInstance⟩

end PushforwardExactAffine


-- created on 2026-10-23
