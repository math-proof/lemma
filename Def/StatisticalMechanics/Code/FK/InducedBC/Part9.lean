module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
public import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
public import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
public import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
public import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
public import Theorem.StatisticalMechanics.Code.FK.IvProperties
public import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
public import Instance.StatisticalMechanics.Code.FK.InducedBC.Part6
open scoped BigOperators
open SimpleGraph
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


noncomputable def fullComponentMap (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    (innerGraph d n ω ψ).ConnectedComponent ⊕ OutsideOnlyComp d n ψ →
      (fullGraph d n ω ψ).ConnectedComponent
  | Sum.inl c => c.lift (fun x => (fullGraph d n ω ψ).connectedComponentMk (boxVertIncl d n x))
      (fun a b p _ => ConnectedComponent.sound
        (fullGraph_reachable_of_innerGraph d n ω ψ p.reachable))
  | Sum.inr c => c.1.lift (fun v => (fullGraph d n ω ψ).connectedComponentMk v)
      (fun a b p _ => ConnectedComponent.sound (p.reachable.mono (outsideGraph_le_fullGraph d n ω ψ)))

end FK
end StatMech
