/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Structure.StatisticalMechanics.Code.Universality.HexBridge.Part3


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexColumnEmb

variable {W I : Type*} (E : HexColumnEmb W I)


noncomputable def fiberSum (v : ℕ) : ℝ :=
  ∑' i : {i // E.scale i = v}, E.wtSAW (E.emb i.1)


end HexColumnEmb
end StatMech.Universality
