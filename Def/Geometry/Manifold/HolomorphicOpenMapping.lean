/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicOpenMapping.lean -/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.RingTheory.PicardGroup
open Set Manifold
open scoped Manifold
open Topology Filter

/-!
# Complex rigidity, open mapping theorem

Nonconstant holomorphic maps between Riemann surfaces are open maps.
-/


namespace MDifferentiable

/-- A finite-dimensional complex normed space of complex dimension one is
continuously linearly equivalent to `ℂ`. -/
noncomputable def linEquivFinrankOne (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (h : Module.finrank ℂ E = 1) : E ≃L[ℂ] ℂ :=
  ContinuousLinearEquiv.ofFinrankEq (h.trans (Module.finrank_self ℂ).symm)

end MDifferentiable
