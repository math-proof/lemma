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
import Def.StatisticalMechanics.Code.FK.PottsClusterSumWeakLimitIdentification.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK

open Lattice Percolation

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem measurable_pottsBoxJointRestrict (d n q : Nat) :
    Measurable (pottsBoxJointRestrict d n q) := by
  have hspin : Measurable (fun joint : PottsJointConfig d q =>
      fun x : boxVerts d n => joint.1 x) :=
    measurable_pi_lambda _ fun x =>
      (measurable_pi_apply (x : Site d)).comp measurable_fst
  have hedge : Measurable (fun joint : PottsJointConfig d q =>
      fun e : Sym2 (boxVerts d n) => joint.2 (edgeIncl d n e)) :=
    measurable_pi_lambda _ fun e =>
      (measurable_pi_apply (edgeIncl d n e)).comp measurable_snd
  exact hspin.prodMk hedge

theorem continuous_pottsBoxJointRestrict (d n q : Nat) :
    Continuous (pottsBoxJointRestrict d n q) := by
  have hspin : Continuous (fun joint : PottsJointConfig d q =>
      fun x : boxVerts d n => joint.1 x) :=
    continuous_pi fun x =>
      (continuous_apply (x : Site d)).comp continuous_fst
  have hedge : Continuous (fun joint : PottsJointConfig d q =>
      fun e : Sym2 (boxVerts d n) => joint.2 (edgeIncl d n e)) :=
    continuous_pi fun e =>
      (continuous_apply (edgeIncl d n e)).comp continuous_snd
  exact hspin.prodMk hedge

theorem reachable_extendEdge_endpoint_mem_box
    {d : Nat} (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) {x y : Site d}
    (hreach : (openSubgraph d (extendEdge d n omega)).Reachable x y)
    (hx : x ∈ box d n) : y ∈ box d n := by
  obtain ⟨walk⟩ := hreach
  induction walk with
  | nil => exact hx
  | @cons u v z huv walk ih =>
      exact ih
        (StatMech.FrontierB.openSubgraph_extendEdge_adj_endpoints_mem_box
          n omega huv).2

theorem cluster_extendEdge_finite
    {d : Nat} (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) (x : boxVerts d n) :
    (cluster d (extendEdge d n omega) (x : Site d)).Finite := by
  apply (box_finite d n).subset
  intro y hy
  exact reachable_extendEdge_endpoint_mem_box n omega
    (mem_cluster.mp hy) x.2

theorem boxComponentRepresentatives_distinct
    {d : Nat} (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n)))
    (C D : (openSub (boxGraph d n) omega).ConnectedComponent)
    (hCD : C ≠ D) :
    ¬Lattice.Connected d (extendEdge d n omega)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega C : boxVerts d n) : Site d)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega D : boxVerts d n) : Site d) := by
  intro hconn
  apply hCD
  rw [← finiteOpenComponentRepresentative_component (boxGraph d n) omega C,
    ← finiteOpenComponentRepresentative_component (boxGraph d n) omega D]
  apply SimpleGraph.ConnectedComponent.sound
  exact (StatMech.FrontierB.openSub_extendEdge_reachable_iff n omega
    (finiteOpenComponentRepresentative (boxGraph d n) omega C)
    (finiteOpenComponentRepresentative (boxGraph d n) omega D)).mpr hconn

set_option maxHeartbeats 3000000 in


theorem boxClusterSumSpin_law
    {d q : Nat} [NeZero q] (boundaryColor : Fin q) (n : Nat)
    (omega : ConfigSpace (Sym2 (boxVerts d n))) :
    Measure.map (fun label (x : boxVerts d n) =>
        pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (x : Site d))
        (pottsIIDLabelMeasure d q) =
      ((PMF.uniformOfFintype
        ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q)).map
          (IsingFK.coloring (boxGraph d n) omega)).toMeasure := by
  let rep : (openSub (boxGraph d n) omega).ConnectedComponent -> Site d :=
    fun C => ((finiteOpenComponentRepresentative (boxGraph d n) omega C :
      boxVerts d n) : Site d)
  have hfinite : ∀ C, (cluster d (extendEdge d n omega) (rep C)).Finite := by
    intro C
    change (cluster d (extendEdge d n omega)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega C :
        boxVerts d n) : Site d)).Finite
    exact cluster_extendEdge_finite n omega
      (finiteOpenComponentRepresentative (boxGraph d n) omega C)
  have hrep := pottsClusterSumSpin_representatives_law boundaryColor
    (extendEdge d n omega) rep hfinite
      (boxComponentRepresentatives_distinct n omega)
  have hfactor : (fun label (x : boxVerts d n) =>
      pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (x : Site d)) =
      IsingFK.coloring (boxGraph d n) omega ∘
        (fun label C =>
          pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (rep C)) := by
    funext label x
    rw [Function.comp_apply, IsingFK.coloring_apply]
    apply Eq.symm
    apply pottsClusterSumSpin_eq_of_connected boundaryColor
    change Lattice.Connected d (extendEdge d n omega)
      ((finiteOpenComponentRepresentative (boxGraph d n) omega
        ((openSub (boxGraph d n) omega).connectedComponentMk x) :
          boxVerts d n) : Site d) (x : Site d)
    apply (StatMech.FrontierB.openSub_extendEdge_reachable_iff n omega
      (finiteOpenComponentRepresentative (boxGraph d n) omega
        ((openSub (boxGraph d n) omega).connectedComponentMk x)) x).mp
    apply SimpleGraph.ConnectedComponent.exact
    exact finiteOpenComponentRepresentative_component (boxGraph d n) omega _
  have hinner : Measurable (fun label : Site d -> Fin q => fun C =>
      pottsClusterSumSpin boundaryColor (extendEdge d n omega) label (rep C)) :=
    measurable_pi_lambda _ fun C =>
      (measurable_pottsClusterSumSpin_apply boundaryColor (rep C)).comp
        (measurable_const.prodMk measurable_id)
  rw [hfactor, ← Measure.map_map Measurable.of_discrete hinner, hrep]
  rw [Measure.infinitePi_eq_pi, pottsUniformPi_eq_uniform]
  exact PMF.toMeasure_map (IsingFK.coloring (boxGraph d n) omega)
    (PMF.uniformOfFintype
      ((openSub (boxGraph d n) omega).ConnectedComponent -> Fin q))
      Measurable.of_discrete


end StatMech.FK
