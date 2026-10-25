/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/InverseLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Constructions
import Mathlib.Order.DirectedInverseSystem
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import Def.v1.Atlas.NumberTheoryI.code.InverseLimits


noncomputable section

open Set

section AdicCompletionTopology

omit hp in
theorem digitPartialSum_dvd (b : ℕ → ℕ) (n : ℕ) :
    (p : ℤ) ^ n ∣ (digitPartialSum p b (n + 1) : ℤ) - (digitPartialSum p b n : ℤ) := by
  simp only [digitPartialSum]
  push_cast
  ring_nf
  exact dvd_mul_right _ _

end AdicCompletionTopology
end
