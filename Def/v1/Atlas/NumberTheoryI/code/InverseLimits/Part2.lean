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
import Theorem.v1.Atlas.NumberTheoryI.code.InverseLimits.Part3


noncomputable section

open Set

section AdicCompletionTopology

noncomputable def padicIntOfDigits (b : ℕ → ℕ) (_hb : ∀ i, b i < p) : ℤ_[p] :=
  PadicInt.ofIntSeq (fun n => (digitPartialSum p b n : ℤ))
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub _ p (digitPartialSum_dvd b))

end AdicCompletionTopology
end
