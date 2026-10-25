-- Carved instances; Definitions owns SmoothProperCurve API.
import Lemma.AlgebraicGeometry.SmoothProperCurveBase
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Fiber

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry
instance SmoothOfRelativeDimension.smooth_one {X S : Scheme.{u}} (f : X ⟶ S)
    [SmoothOfRelativeDimension 1 f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 1 f
end AlgebraicGeometry
