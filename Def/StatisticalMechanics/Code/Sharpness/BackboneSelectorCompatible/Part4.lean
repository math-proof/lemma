/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2Quantitative
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part3
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]


noncomputable def shb_backboneNumSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (p : G.Path x y) : ℝ :=
  ∑' m : G.edgeFinset → ℕ,
    if sources G (ofEdgeFun G m) = {x, y} ∧
        shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then
      weight G β J (ofEdgeFun G m) else 0


noncomputable def shb_rhoSupport
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (x y : V) (p : G.Path x y) : ℝ :=
  shb_backboneNumSupport G β J x y p / currentSum G β J ∅


end StatMech.Sharpness
