/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyProof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyInstance
import Lemma.Submodule.EqSwapComplement.of.In.IsCompl.IsCompl

namespace GeometricAlgebra

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two flags opposite to the same flag `F` necessarily share the same length. -/
theorem opposite_flags_same_len (F F'₁ F'₂ : Flag k V)
    (h₁ : Flag.isOppositeFlag F F'₁)
    (h₂ : Flag.isOppositeFlag F F'₂) :
    F'₁.len = F'₂.len := by
  have := h₁.1; have := h₂.1; omega
