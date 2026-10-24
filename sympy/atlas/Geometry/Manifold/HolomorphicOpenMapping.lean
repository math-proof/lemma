/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicOpenMapping.lean -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.RingTheory.PicardGroup

/-!
# Complex rigidity, open mapping theorem

Nonconstant holomorphic maps between Riemann surfaces are open maps.
-/

open Set Manifold
open scoped Manifold
open Topology Filter

namespace MDifferentiable

/-- A finite-dimensional complex normed space of complex dimension one is
continuously linearly equivalent to `ℂ`. -/
private noncomputable def linEquivFinrankOne (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : Module.finrank ℂ E = 1) : E ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.ofFinrankEq (h.trans (Module.finrank_self ℂ).symm)
end MDifferentiable
namespace MathlibExt.Geometry.Manifold.ComplexRigidityWanted
end MathlibExt.Geometry.Manifold.ComplexRigidityWanted
