/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail.Part2
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

theorem PeriodicGraph.tailComponentVertices_infinite
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) (hD : D.supp.Infinite) :
    (P.tailComponentVertices omega x K D).Infinite :=
  hD.image Subtype.val_injective.injOn

theorem PeriodicGraph.tailComponentVertices_subset_cluster
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) :
    P.tailComponentVertices omega x K D ⊆ P.cluster omega x := by
  rintro _ ⟨y, _, rfl⟩
  exact y.2

theorem PeriodicGraph.tailComponentVertices_connected_outside
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (K : Finset V)
    (D : (P.tailClusterGraph omega x).ComponentCompl
      (P.tailClusterCut omega x K)) :
    ∀ u ∈ P.tailComponentVertices omega x K D,
      ∀ v ∈ P.tailComponentVertices omega x K D,
        ∃ (hu : u ∉ (K : Set V)) (hv : v ∉ (K : Set V)),
          ((P.openSubgraph omega).induce (K : Set V)ᶜ).Reachable
            ⟨u, hu⟩ ⟨v, hv⟩ := by
  rintro u ⟨uC, huD, rfl⟩ v ⟨vC, hvD, rfl⟩
  rcases huD with ⟨huCut, huComp⟩
  rcases hvD with ⟨hvCut, hvComp⟩
  have huK : uC.1 ∉ (K : Set V) := by
    intro hmem
    exact huCut (by simp [PeriodicGraph.tailClusterCut, hmem])
  have hvK : vC.1 ∉ (K : Set V) := by
    intro hmem
    exact hvCut (by simp [PeriodicGraph.tailClusterCut, hmem])
  refine ⟨huK, hvK, ?_⟩
  have hreach :
      ((P.tailClusterGraph omega x).induce
        ((P.tailClusterCut omega x K : Set (P.TailClusterVertex omega x)))ᶜ).Reachable
          ⟨uC, huCut⟩ ⟨vC, hvCut⟩ := by
    rw [← SimpleGraph.ConnectedComponent.eq]
    exact huComp.trans hvComp.symm
  let f : ((P.tailClusterGraph omega x).induce
      ((P.tailClusterCut omega x K : Set (P.TailClusterVertex omega x)))ᶜ) →g
      ((P.openSubgraph omega).induce (K : Set V)ᶜ) := {
    toFun := fun z => ⟨z.1.1, by
      intro hzK
      exact z.2 (by simp [PeriodicGraph.tailClusterCut, hzK])⟩
    map_rel' := by intro a b hab; exact hab }
  exact hreach.map f

end StatMech.FK.PeriodicPlanar
