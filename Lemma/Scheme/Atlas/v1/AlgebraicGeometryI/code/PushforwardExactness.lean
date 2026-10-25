import Mathlib
import sympy.Basic
import Instance.v1.Atlas.AlgebraicGeometryI.code.PushforwardExactness.Part2
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopCat PushforwardExactness


namespace PushforwardExactness

/--
[pushforward_affine_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardExactness.lean)
-/
@[path]
lemma pushforward_affine_exact
  {R S : Type v}
  [CommRing R]
  [CommRing S]
  {phi : R →+* S} :
-- imply
  PreservesFiniteLimits (ModuleCat.restrictScalars.{v} phi) ∧ PreservesFiniteColimits (ModuleCat.restrictScalars.{v} phi) :=
-- proof
  ⟨inferInstance, inferInstance⟩

end PushforwardExactness


-- created on 2026-10-23
