/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Manifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.Manifolds.Part2


noncomputable section

open scoped Topology

open LinearMap (ker range)

open Set Filter

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsPartialParametrization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : Set E) where
  ambientNhd : Set E
  ambientNhd_open : IsOpen ambientNhd
  paramDomain : Set F
  paramDomain_open : IsOpen paramDomain
  f : F → E
  smooth : ContDiffOn ℝ ⊤ f paramDomain
  injective : Set.InjOn f paramDomain
  image_eq : f '' paramDomain = M ∩ ambientNhd
  immersion : ∀ x ∈ paramDomain, Function.Injective (fderiv ℝ f x)

end Hypersurface
end
