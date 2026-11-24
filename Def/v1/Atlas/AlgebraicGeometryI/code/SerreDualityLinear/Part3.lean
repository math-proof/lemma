module
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.CohomologyP1.Part2
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.CohomologyP1
public import Theorem.v1.Atlas.AlgebraicGeometryI.code.SerreDualityLinear.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SerreDualityLinear.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SerreDualityP1

open CohomologyP1


/-- The `k`-linear involution `(ℤ →₀ k) ≃ₗ[k] (ℤ →₀ k)` induced by the residue shift. -/
noncomputable def shiftEquiv (k : Type*) [Field k] : (ℤ →₀ k) ≃ₗ[k] (ℤ →₀ k) :=
  LinearEquiv.ofInvolutive (shiftMap k) (shiftMap_involutive k)

end SerreDualityP1
