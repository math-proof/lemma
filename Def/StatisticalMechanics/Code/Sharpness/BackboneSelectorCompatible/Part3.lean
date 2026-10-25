/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


def shb_CurrentSupportedOn (H : SimpleGraph V) (n : Current V) : Prop :=
  ∀ e, n e ≠ 0 → e ∈ H.edgeSet


noncomputable def shb_restrictBackbonePath
    {H G : SimpleGraph V} [DecidableRel G.Adj]
    (hHG : H ≤ G) (n : Current V) (hSupp : shb_CurrentSupportedOn H n)
    {x y : V} (p : G.Path x y) (hp : shb_IsBackboneOf G n x y p) :
    H.Path x y := by
  have he : ∀ e ∈ p.1.edges, e ∈ H.edgeSet := by
    intro e he
    exact hSupp e (Nat.ne_of_gt (hp e he).pos)
  exact ⟨p.1.transfer H he, p.2.transfer he⟩


end StatMech.Sharpness
