/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumWeakLimitIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumContinuity.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part2
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteOpenComponentVertices_nonempty
    (omega : ConfigSpace (Sym2 V))
    (C : (openSub G omega).ConnectedComponent) :
    (finiteOpenComponentVertices G omega C).Nonempty := by
  induction C using SimpleGraph.ConnectedComponent.ind with
  | _ x =>
      exact ⟨x, by simp [finiteOpenComponentVertices]⟩

theorem finiteOpenComponentVertices_disjoint
    (omega : ConfigSpace (Sym2 V))
    (C D : (openSub G omega).ConnectedComponent) (hCD : C ≠ D) :
    Disjoint (finiteOpenComponentVertices G omega C)
      (finiteOpenComponentVertices G omega D) := by
  apply Finset.disjoint_left.mpr
  intro x hxC hxD
  simp only [finiteOpenComponentVertices, Finset.mem_filter, Finset.mem_univ,
    true_and] at hxC hxD
  exact hCD (hxC.symm.trans hxD)


theorem finiteOpenComponentSums_law
    (q : Nat) [NeZero q] (omega : ConfigSpace (Sym2 V)) :
    Measure.map (finiteOpenComponentSums G omega)
        (PMF.uniformOfFintype (V -> Fin q)).toMeasure =
      (PMF.uniformOfFintype
        ((openSub G omega).ConnectedComponent -> Fin q)).toMeasure := by
  have h := pottsIID_blockSums_law (q := q)
    (finiteOpenComponentVertices G omega)
    (finiteOpenComponentVertices_nonempty G omega)
    (finiteOpenComponentVertices_disjoint G omega)
  rw [Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform,
    Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform] at h
  exact h


theorem finiteOpenComponentSums_pmf
    (q : Nat) [NeZero q] (omega : ConfigSpace (Sym2 V)) :
    (PMF.uniformOfFintype (V -> Fin q)).map
        (finiteOpenComponentSums G omega) =
      PMF.uniformOfFintype
        ((openSub G omega).ConnectedComponent -> Fin q) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (finiteOpenComponentSums G omega)
    (PMF.uniformOfFintype (V -> Fin q)) Measurable.of_discrete]
  exact finiteOpenComponentSums_law G q omega


theorem freeSiteClusterSumJointPMF_eq_ivp_freeJointPMF
    (q : Nat) [NeZero q] {p : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < (q : Real)) :
    (fkPMF G hp hp1 hq).bind (fun omega =>
      (PMF.uniformOfFintype (V -> Fin q)).map fun label =>
        (IsingFK.coloring G omega
          (finiteOpenComponentSums G omega label), omega)) =
      ivp_freeJointPMF G q hp hp1 hq := by
  rw [← freeClusterColorJointPMF_eq_ivp_freeJointPMF G q hp hp1 hq]
  unfold freeClusterColorJointPMF
  apply congrArg (PMF.bind (fkPMF G hp hp1 hq))
  funext omega
  change (PMF.uniformOfFintype (V -> Fin q)).map
      ((fun tau => (IsingFK.coloring G omega tau, omega)) ∘
        finiteOpenComponentSums G omega) = _
  rw [← PMF.map_comp]
  rw [finiteOpenComponentSums_pmf G q omega]


end StatMech.FK
