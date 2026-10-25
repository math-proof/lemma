/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Abbrev.v1.Atlas.TensorCategories.code.QuantumSl2
set_option maxHeartbeats 400000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


namespace QuantumSl2

variable {k : Type u} [Field k] {A : Type v} [Ring A] [HopfAlgebra k A] [h : QuantumSl2 k A]


/-- The Cartan-type element `(q - q^{-1})^{-1} · (K - K^{-1})` of the quantum group. -/
noncomputable def cartanElement : A :=
  (h.q - (h.q)⁻¹)⁻¹ • (h.K - h.Kinv)

end QuantumSl2
