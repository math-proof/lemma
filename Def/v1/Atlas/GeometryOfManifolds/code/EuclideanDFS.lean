/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.Analysis.Normed.Module.Alternating.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.Alternating.Curry
import Mathlib.LinearAlgebra.Multilinear.Curry
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Abbrev.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS


noncomputable section

/-- The space $\Omega^p(\mathbb{R}^n)$ of (not-necessarily-smooth) differential $p$-forms on
$\mathbb{R}^n$: pointwise alternating $\mathbb{R}$-multilinear maps
$(\mathbb{R}^n)^p \to \mathbb{R}$. -/
def EuclideanΩ (n : ℕ) (p : ℕ) :=
  Eℝ n → (Eℝ n [⋀^Fin p]→ₗ[ℝ] ℝ)

/-- The space of vector fields $\mathfrak{X}(\mathbb{R}^n)$ on Euclidean space: arbitrary maps
$\mathbb{R}^n \to \mathbb{R}^n$. -/
def EuclideanVF (n : ℕ) :=
  Eℝ n → Eℝ n

end
