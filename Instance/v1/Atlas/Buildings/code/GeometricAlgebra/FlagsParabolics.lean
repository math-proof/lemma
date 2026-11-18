/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/FlagsParabolics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic.Group
public import Class.v1.Atlas.Buildings.code.GeometricAlgebra.FlagsParabolics.Part2

@[expose] public section

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- The existence property `SemidirectExistenceProperty` together with the
unique-decomposition lemma `Flag.unique_decomp_linear_proof` yields the combined
`SemidirectDecompositionProperty`. -/
instance instSemidirectDecompositionProperty [SemidirectExistenceProperty k V] :
    SemidirectDecompositionProperty k V where
  exists_decomp_linear := SemidirectExistenceProperty.exists_decomp_linear
  unique_decomp_linear := fun F F' hopp hlen hcov d₁ d₂ u₁ u₂
    hd₁F hd₁F' hd₂F hd₂F' hu₁F hu₁U hu₂F hu₂U hcomp =>
    Flag.unique_decomp_linear_proof F F' hopp hlen hcov
      d₁ d₂ u₁ u₂ hd₁F hd₁F' hd₂F hd₂F' hu₁F hu₁U hu₂F hu₂U hcomp


end GeometricAlgebra
