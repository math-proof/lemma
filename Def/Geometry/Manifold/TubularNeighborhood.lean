/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/TubularNeighborhood.lean -/

-- Author: @toskua, Avocado

import Mathlib.Geometry.Manifold.SmoothEmbedding
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Geometry.Manifold.Sheaf.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linarith
open Manifold Topology Filter Metric
open scoped Manifold ContDiff


-- N0: coordinate normal-equation map (avoids semilinear innerSL typing issue)
noncomputable def normalEqMapCoord
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (γ : E → F) : F × E → (Fin (Module.finrank ℝ E) → ℝ) :=
  fun q i => inner ℝ (q.1 - γ q.2) ((fderiv ℝ γ q.2) ((Module.finBasis ℝ E) i))

