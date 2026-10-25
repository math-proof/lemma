/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FiniteActiveDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredWeights.Part4
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.FK.FiniteActiveDuality.Part2
open Finset SimpleGraph
open scoped BigOperators


namespace StatMech.FK

open Lattice

noncomputable section

variable {V W : Type*} [Fintype V] [Fintype W]
  [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph V) (H : SimpleGraph W)
  [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem openCount_extendActive_eq_activeOpenCount
    (omega : ConfigSpace G.edgeSet) :
    openCount G (extendActive G omega) = activeOpenCount G omega := by
  let E : {e : G.edgeFinset // extendActive G omega e.1 = true} ≃
      {e : G.edgeSet // omega e = true} :=
    Equiv.subtypeEquiv (edgeFinsetEdgeSetEquiv G) (fun e => by
      simpa [edgeFinsetEdgeSetEquiv] using
        extendActive_apply G omega (edgeFinsetEdgeSetEquiv G e))
  have hcard := Fintype.card_congr E
  unfold openCount activeOpenCount
  rw [← hcard, Fintype.card_subtype]
  rw [show (Finset.univ : Finset G.edgeFinset) =
      G.edgeFinset.attach by ext; simp]
  have hf := congrArg Finset.card
    (Finset.filter_attach
      (fun e : Sym2 V => extendActive G omega e = true) G.edgeFinset)
  simpa using hf.symm


theorem activeOpenCount_dualConfig
    (edgeDual : G.edgeSet ≃ H.edgeSet)
    (omega : ConfigSpace G.edgeSet) :
    activeOpenCount H (activeDualConfig G H edgeDual omega) =
      Fintype.card G.edgeSet - activeOpenCount G omega := by
  unfold activeOpenCount
  rw [← Fintype.card_subtype_compl (fun e : G.edgeSet => omega e = true)]
  let E : {e : G.edgeSet // ¬ omega e = true} ≃
      {f : H.edgeSet // activeDualConfig G H edgeDual omega f = true} :=
    Equiv.subtypeEquiv edgeDual (fun e => by simp)
  have hcard := Fintype.card_congr E
  exact hcard.symm

theorem activeWeight_eq_count (p q : Real)
    (omega : ConfigSpace G.edgeSet) :
    activeWeight G (fun _ => p) q omega =
      BeffaraDC.edgeProductCount p (Fintype.card G.edgeSet)
          (activeOpenCount G omega) *
        q ^ numClusters G (extendActive G omega) := by
  unfold activeWeight fkWeightW
  change edgeProduct G p (extendActive G omega) * _ = _
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    openCount_extendActive_eq_activeOpenCount]
  rw [SimpleGraph.edgeFinset_card]

theorem wiredActiveWeight_eq_count
    (boundary : W → Prop) [DecidablePred boundary]
    (p q : Real) (eta : ConfigSpace H.edgeSet) :
    PeriodicPlanar.wiredActiveWeight H boundary p q eta =
      BeffaraDC.edgeProductCount p (Fintype.card H.edgeSet)
          (activeOpenCount H eta) *
        q ^ numClustersWired H boundary (extendActive H eta) := by
  unfold PeriodicPlanar.wiredActiveWeight wiredFkWeight
  rw [BeffaraDC.dlt_edgeProduct_eq_count,
    openCount_extendActive_eq_activeOpenCount]
  rw [SimpleGraph.edgeFinset_card]


end
end StatMech.FK
