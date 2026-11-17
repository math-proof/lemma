/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/TubularNeighborhood.lean -/

-- Author: @toskua, Avocado

module

public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Instances.Real
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Linarith

@[expose] public section

open Manifold Topology Filter Metric
open scoped Manifold ContDiff


-- N0: coordinate normal-equation map (avoids semilinear innerSL typing issue)
noncomputable def normalEqMapCoord
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (γ : E → F) : F × E → (Fin (Module.finrank ℝ E) → ℝ) :=
  fun q i => inner ℝ (q.1 - γ q.2) ((fderiv ℝ γ q.2) ((Module.finBasis ℝ E) i))

