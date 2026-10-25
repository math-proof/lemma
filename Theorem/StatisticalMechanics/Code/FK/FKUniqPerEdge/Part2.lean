/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.FKUniqPerEdge
open Set Filter Topology
open scoped BigOperators
open StatMech.FK

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Lattice

variable {d : ℕ}


theorem fpe2_perEdgeG_convex (d N : ℕ) {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (e' : Sym2 (boxVerts d N)) :
    ConvexOn ℝ univ (fpe2_perEdgeG d N G e') := by
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [if_pos he']; exact hG
  · rw [if_neg he']; exact fpe2_halfLin_convex


theorem fpe2_ha_eq (d N : ℕ) {G : ℝ → ℝ}
    (hfree : fpe2_GenuineFreeIsLeftDeriv d N G)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    edgeMargProb (fuc_freeMass d N t) e' = pressureLeftDeriv (fpe2_perEdgeG d N G e') t := by
  rw [fuc_edgeMargProb_free]
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [if_pos he']; exact hfree e' he' t
  · rw [if_neg he', fpe2_halfLin_leftDeriv]
    exact fpe2_free_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)


theorem fpe2_hb_eq (d N : ℕ) {G : ℝ → ℝ}
    (hwired : fpe2_GenuineWiredIsRightDeriv d N G)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    edgeMargProb (fuc_wiredMass d N t) e' = pressureRightDeriv (fpe2_perEdgeG d N G e') t := by
  rw [fuc_edgeMargProb_wired]
  unfold fpe2_perEdgeG
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · rw [if_pos he']; exact hwired e' he' t
  · rw [if_neg he', fpe2_halfLin_rightDeriv]
    exact fpe2_wired_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)


theorem fpe2_wired_genuine_eq_ref (hd : 0 < d) (N : ℕ)
    {eb e' : Sym2 (boxVerts d N)} (he' : e' ∈ (boxGraph d N).edgeFinset)
    (heb : eb ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    edgeMargProb (fuc_wiredMass d N t) e' = edgeMargProb (fuc_wiredMass d N t) eb := by
  rw [fuc_edgeMargProb_wired, fuc_edgeMargProb_wired,
    rot_wired_box_edge_const hd N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t),
    rot_wired_box_edge_const hd N eb heb (fsc_logistic_pos t) (fsc_logistic_lt_one t)]


theorem fpe2_hlink (hd : 0 < d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) :
    ∀ t : ℝ, ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) eb) t →
      ∀ e' : Sym2 (boxVerts d N),
        ContinuousAt (fun t => edgeMargProb (fuc_wiredMass d N t) e') t := by
  intro t hcont e'
  by_cases he' : e' ∈ (boxGraph d N).edgeFinset
  · 
    have heq : (fun t => edgeMargProb (fuc_wiredMass d N t) e')
        = fun t => edgeMargProb (fuc_wiredMass d N t) eb :=
      funext (fun t => fpe2_wired_genuine_eq_ref hd N he' heb t)
    rw [heq]; exact hcont
  · 
    have heq : (fun t => edgeMargProb (fuc_wiredMass d N t) e') = fun _ => (1/2 : ℝ) := by
      funext t
      rw [fuc_edgeMargProb_wired]
      exact fpe2_wired_density_nonEdge N e' he' (fsc_logistic_pos t) (fsc_logistic_lt_one t)
    rw [heq]; exact continuousAt_const


theorem fpe2_fk_uniqueness_of_genuine (hd : 0 < d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset) {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hfree : fpe2_GenuineFreeIsLeftDeriv d N G)
    (hwired : fpe2_GenuineWiredIsRightDeriv d N G) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  choose P hP using fuc_hcoup d N
  exact fud_countable_phi_ne_of_convexPerEdge
    (fun t => fuc_freeMass d N t) (fun t => fuc_wiredMass d N t) eb P hP
    (fuc_hmono d N eb)
    (fpe2_perEdgeG d N G) (fpe2_perEdgeG_convex d N hG)
    (fpe2_ha_eq d N hfree) (fpe2_hb_eq d N hwired)
    (fpe2_hlink hd N eb heb)


end FK
end StatMech
