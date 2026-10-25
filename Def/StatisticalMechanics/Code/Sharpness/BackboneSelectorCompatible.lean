/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


@[reducible] noncomputable def shb_supportPathOrder (G : SimpleGraph V) (x y : V) :
    LinearOrder (G.Path x y) :=
  LinearOrder.lift' (fun p => p.1.support) (by
    intro p q h
    apply Subtype.ext
    exact SimpleGraph.Walk.support_injective h)


noncomputable def shb_backboneSelectSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n : Current V) (x y : V) : Option (G.Path x y) := by
  letI := shb_supportPathOrder G x y
  exact if h : (shb_backboneSet G n x y).Nonempty then
    some ((shb_backboneSet G n x y).min' h) else none


end StatMech.Sharpness
