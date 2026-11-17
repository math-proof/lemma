/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/HolomorphicOpenMapping.lean -/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.Notation
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

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
