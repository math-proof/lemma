/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/SubmersionOfSurjectiveMFDeriv.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.LocalDiffeomorph
open scoped Topology ContDiff
open Manifold

/-!
# Submersions from surjective manifold derivatives

This file proves that a map from a Banach manifold to a finite-dimensional manifold over `ℝ` or
`ℂ` is a submersion at a point when it is smooth on a neighbourhood and its manifold derivative
there is surjective, and derives the finite-dimensional criterion.
-/


noncomputable section

def submersionSurj_modelPartialDiffeomorph
    {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) [I.Boundaryless] (n : ℕ∞ω) :
    PartialDiffeomorph I 𝓘(𝕜, E) H E n where
  toPartialEquiv := I.toHomeomorph.toPartialEquiv
  open_source := by simp
  open_target := by simp
  contMDiffOn_toFun := I.contMDiff.contMDiffOn
  contMDiffOn_invFun := by
    simpa [ModelWithCorners.toHomeomorph, I.range_eq_univ] using
      (I.contMDiffOn_symm (n := n))

end
