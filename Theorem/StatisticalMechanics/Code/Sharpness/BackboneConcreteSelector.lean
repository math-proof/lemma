/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Instance.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector
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


@[simp] theorem bondwiseSuffixEvent_nil
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : Nat -> Bool) (m : G.edgeFinset -> Nat) :
    BondwiseSuffixEvent G X x [] bit m := by
  simp [BondwiseSuffixEvent]


theorem no_nilFiber_iff_bondwiseSuffixEvent_of_sources_ne_empty
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : Nat -> Bool)
    (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅) :
    ¬(S.Fiber d [] m ↔ BondwiseSuffixEvent d.graph X x [] bit m) := by
  intro hbridge
  have hfiber : S.Fiber d [] m := hbridge.mpr (bondwiseSuffixEvent_nil _ _ _ _ _)
  exact hsrc ((S.select?_eq_some_nil_iff d m).mp hfiber)


theorem no_functional_fiber_bridge_of_nonempty_event
    (S : shb_PartialCurrentDynamicSelector (V := V))
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (bit : Nat -> Bool) (bonds : List (Sym2 V))
    (decode : List (Sym2 V) -> List (shb_ExplorationSegment V))
    (hdecode : decode [] ≠ decode bonds)
    (hbonds : BondwiseSuffixEvent d.graph X x bonds bit m)
    (hbridge : forall bs,
      S.Fiber d (decode bs) m <->
        BondwiseSuffixEvent d.graph X x bs bit m) : False := by
  have hnil : S.select? d m = some (decode []) :=
    (hbridge []).mpr (bondwiseSuffixEvent_nil _ _ _ _ _)
  have hword : S.select? d m = some (decode bonds) :=
    (hbridge bonds).mpr hbonds
  apply hdecode
  exact Option.some.inj (hnil.symm.trans hword)


end BackboneConcreteSelector
end
end StatMech.Sharpness
