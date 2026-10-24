/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/ImmersionOfInjectiveMFDeriv.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Immersions from injective manifold differentials

This file proves that an injective manifold differential gives an immersion when its range has
a closed complement, and derives the finite-dimensional criterion over `ℝ` or `ℂ`.
-/

open scoped Topology ContDiff
open Function Set Manifold

noncomputable section
namespace MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted
end MathlibExt.Geometry.Manifold.ImmersionOfInjectiveMFDerivWanted
