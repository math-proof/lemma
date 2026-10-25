/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Instance.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


structure BondwiseRunSpec (V : Type*) [Fintype V] [DecidableEq V] where
  State : Type*
  scan : shb_DynamicEdgeExploration State (Sym2 V)
  state : State
  suffix : List (Sym2 V)
  bit : Nat -> Bool
  terminal : State -> (Sym2 V -> Option Nat) -> Prop


end BackboneConcreteSelector
end
end StatMech.Sharpness
