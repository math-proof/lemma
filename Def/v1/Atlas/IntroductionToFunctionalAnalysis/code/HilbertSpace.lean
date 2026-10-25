/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToFunctionalAnalysis/code/HilbertSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.OfNorm
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Abbrev.v1.Atlas.IntroductionToFunctionalAnalysis.code.HilbertSpace
open scoped InnerProductSpace


namespace HilbertSpace

section NormFromInner

variable {𝕜 : Type*} [RCLike 𝕜]

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- An inner product (given as `InnerProductSpace.Core` data) induces a `NormedAddCommGroup`
structure on $H$ via the norm $\|v\| = \langle v, v \rangle^{1/2}$. Hence, if $H$ is a pre-Hilbert
space, then $\|\cdot\|$ is a genuine norm on $H$. -/
@[reducible]
noncomputable def normedAddCommGroupOfInnerProduct
    (𝕜 : Type*) (H : Type*) [RCLike 𝕜] [AddCommGroup H] [Module 𝕜 H]
    (c : InnerProductSpace.Core 𝕜 H) : NormedAddCommGroup H :=
  @InnerProductSpace.Core.toNormedAddCommGroup 𝕜 H _ _ _ c

end NormFromInner
end HilbertSpace
