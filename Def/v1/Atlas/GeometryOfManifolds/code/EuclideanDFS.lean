/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanDFS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Analysis.Normed.Module.Alternating.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Normed.Module.Alternating.Curry
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
public import Abbrev.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS

@[expose] public section

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
