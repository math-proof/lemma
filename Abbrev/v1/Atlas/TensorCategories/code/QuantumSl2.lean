/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.TensorProduct
import Class.v1.Atlas.TensorCategories.code.QuantumSl2
set_option maxHeartbeats 400000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


/-- Reference abbreviation for Definition 1.25.1: the quantum group `U_q(sl_2)`. -/
abbrev Definition_1_25_1 (k : Type u) [Field k] (A : Type v) [Ring A] [HopfAlgebra k A] :=
  QuantumSl2 k A

