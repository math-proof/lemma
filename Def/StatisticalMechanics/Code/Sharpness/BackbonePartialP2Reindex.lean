/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialP2Reindex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part6
import Instance.StatisticalMechanics.Code.Sharpness.BackbonePartialP2Reindex
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


noncomputable def rawSourcePairFiberMass (beta : Real)
    (J : Sym2 V -> Real) (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] : Real :=
  rawPairFiberMass G beta J m
    (fun p => sources G (ofEdgeFun G p) = A ∧ Q p) R


noncomputable def labeledSourcePairFiberMass (beta : Real)
    (J : Sym2 V -> Real) (m : G.edgeFinset -> Nat) (A : Finset V)
    (Q R : (G.edgeFinset -> Nat) -> Prop)
    [DecidablePred Q] [DecidablePred R] : Real :=
  ∑ S : Fiber G m A (fun S =>
      Q (profileFlux G m S) ∧ R (profileFlux G m (univ \ S))),
    labeledWeight G beta J m S.1


end BackboneLabeledSwitching
end
end StatMech.Sharpness
