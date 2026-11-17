/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Analysis.InnerProductSpace.OfNorm
public import Mathlib.Analysis.InnerProductSpace.Orthonormal
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Metrizable.Basic
public import Mathlib.Topology.Algebra.Module.Basic
@[expose] public section

open scoped InnerProductSpace


namespace HilbertSpace

/-- A **pre-Hilbert space** is a vector space over $\mathbb{K} = \mathbb{R}, \mathbb{C}$ equipped
with a Hermitian inner product $\langle \cdot, \cdot \rangle : H \times H \to \mathbb{K}$ satisfying
linearity in the first argument, conjugate symmetry, and positive-definiteness. In Mathlib this is
modeled by `InnerProductSpace 𝕜 H`. -/
abbrev PreHilbertSpace (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [SeminormedAddCommGroup H] :=
  InnerProductSpace 𝕜 H

end HilbertSpace
