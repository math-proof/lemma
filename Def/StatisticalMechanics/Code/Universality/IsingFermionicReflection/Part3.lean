/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflection.Part2
open Filter Metric Set Topology


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

namespace FKIsingCaratheodoryApproximation

variable (A : FKIsingCaratheodoryApproximation)


noncomputable def reflect : FKIsingCaratheodoryApproximation where
  U := reflectComplexSet A.U
  root := (starRingEnd Complex) A.root
  root_mem := by simp [A.root_mem]
  isOpen := reflectComplexSet_isOpen A.isOpen
  isPreconnected := reflectComplexSet_isPreconnected A.isPreconnected
  carrier := fun n ↦ reflectComplexSet (A.carrier n)
  mesh := A.mesh
  mesh_pos := A.mesh_pos
  mesh_tendsto_zero := A.mesh_tendsto_zero
  compact_eventually_mem := by
    intro K hK hKU
    have hreflectK : IsCompact (reflectComplexSet K) :=
      reflectComplexSet_isCompact hK
    have hreflectKU : reflectComplexSet K ⊆ A.U := by
      intro z hz
      rw [mem_reflectComplexSet] at hz
      have := hKU hz
      simpa using (mem_reflectComplexSet.mp this)
    filter_upwards [A.compact_eventually_mem
      (reflectComplexSet K) hreflectK hreflectKU] with n hn
    intro z hz
    rw [mem_reflectComplexSet]
    exact hn (mem_reflectComplexSet.mpr (by simpa using hz))
  exterior_eventually_avoided := by
    intro z hz
    have hz' : (starRingEnd Complex) z ∉ closure A.U := by
      intro h
      apply hz
      rw [closure_reflectComplexSet]
      simp [h]
    obtain ⟨r, hr, havoid⟩ :=
      A.exterior_eventually_avoided ((starRingEnd Complex) z) hz'
    refine ⟨r, hr, ?_⟩
    filter_upwards [havoid] with n hn
    rw [Set.disjoint_left]
    intro w hwBall hwCarrier
    rw [mem_reflectComplexSet] at hwCarrier
    have hconjBall : (starRingEnd Complex) w ∈
        ball ((starRingEnd Complex) z) r := by
      simpa [mem_ball, Complex.dist_conj_conj] using hwBall
    exact Set.disjoint_left.1 hn hconjBall hwCarrier
  P := A.P
  M := A.M
  fintypeM := A.fintypeM
  decEqM := A.decEqM
  dobrushin := fun n ↦
    @FKIsingDobrushinDomain.reflect (A.P n) (A.M n)
      (A.fintypeM n) (A.decEqM n) (A.dobrushin n)
  vertexEmbedding := fun n v ↦ (starRingEnd Complex) (A.vertexEmbedding n v)
  medialEmbedding := fun n e ↦ (starRingEnd Complex) (A.medialEmbedding n e)
  vertex_mem_carrier := by
    intro n v
    simp [A.vertex_mem_carrier n v]
  medial_mem_carrier := by
    intro n e
    simp [A.medial_mem_carrier n e]
  carrier_near_medial := by
    intro n z hz
    rw [mem_reflectComplexSet] at hz
    obtain ⟨e, he⟩ :=
      A.carrier_near_medial n ((starRingEnd Complex) z) hz
    refine ⟨e, ?_⟩
    calc
      dist z ((starRingEnd Complex) (A.medialEmbedding n e)) =
          dist ((starRingEnd Complex) z) (A.medialEmbedding n e) := by
        simpa using
          (Complex.dist_conj_comm z (A.medialEmbedding n e)).symm
      _ ≤ A.mesh n := he
  medialEmbedding_eq_position := by
    intro n e
    simp only [FKIsingDobrushinDomain.reflect_medialPosition]
    exact congrArg (starRingEnd Complex) (A.medialEmbedding_eq_position n e)
  rawInterpolant := fun n z ↦ A.rawInterpolant n ((starRingEnd Complex) z)
  rawInterpolant_medial := by
    intro n e
    simpa using A.rawInterpolant_medial n e

end FKIsingCaratheodoryApproximation
end
end StatMech.Universality
