/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part4
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneLabeledSwitching

open FluxEdgeCopy

open RandomCurrent

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def rawSplitWeight (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (K : {p : G.edgeFinset -> Nat // p <= m}) : Real :=
  weight G beta J (ofEdgeFun G K.1) *
    weight G beta J (ofEdgeFun G (fun e => m e - K.1 e))


noncomputable def rawFiberMass (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q : (G.edgeFinset -> Nat) -> Prop) [DecidablePred Q] : Real :=
  ∑ K : {p : G.edgeFinset -> Nat // p <= m},
    if sources G (ofEdgeFun G K.1) = A ∧ Q K.1 then
      rawSplitWeight G beta J m K else 0


noncomputable def rawPairFiberMass (beta : Real) (J : Sym2 V -> Real)
    (m : G.edgeFinset -> Nat)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] : Real :=
  ∑ K : {p : G.edgeFinset -> Nat // p <= m},
    if Q K.1 ∧ R (fun e => m e - K.1 e) then
      rawSplitWeight G beta J m K else 0


end BackboneLabeledSwitching
end
end StatMech.Sharpness
