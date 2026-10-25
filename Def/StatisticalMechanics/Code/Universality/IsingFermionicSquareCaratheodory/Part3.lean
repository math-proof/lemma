/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareCaratheodory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareBoundaryScaledDomain.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareCaratheodory.Part3


namespace StatMech.Universality

open Filter Set Topology Metric

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC
  StatMech.FrontierD

noncomputable section

noncomputable def fkIsingExpandingSquareCaratheodoryApproximation :
    FKIsingCaratheodoryApproximation where
  U := Set.univ
  root := 0
  root_mem := Set.mem_univ 0
  isOpen := isOpen_univ
  isPreconnected := isPreconnected_univ
  carrier := fkIsingExpandingSquareCarrier
  mesh := fkIsingExpandingSquareMesh
  mesh_pos := fkIsingExpandingSquareMesh_pos
  mesh_tendsto_zero := fkIsingExpandingSquareMesh_tendsto_zero
  compact_eventually_mem := by
    intro K hK _
    exact fkIsingExpandingSquare_compact_eventually_mem K hK
  exterior_eventually_avoided := by
    intro z hz
    simp at hz
  P := fun k ↦ fkSquareBoxPlanar (fkIsingExpandingSquareSide k)
  M := fun k ↦ FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k)
  fintypeM := fun _ ↦ inferInstance
  decEqM := fun _ ↦ inferInstance
  dobrushin := fun k ↦ fkIsingSquareWiredPerturbedDobrushinDomain
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertexEmbedding := fun k _ ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) .source
  medialEmbedding := fun k ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertex_mem_carrier := by
    intro k v
    refine ⟨.source, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  medial_mem_carrier := by
    intro k a
    refine ⟨a, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  carrier_near_medial := by
    intro k z hz
    exact hz
  medialEmbedding_eq_position := by
    intro k a
    rfl
  rawInterpolant := fun k ↦ fkIsingSquareWiredPerturbedRawInterpolant
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  rawInterpolant_medial := by
    intro k a
    exact fkIsingSquareWiredPerturbedRawInterpolant_medial
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a


noncomputable def fkIsingExpandingBoundarySquareCaratheodoryApproximation :
    FKIsingCaratheodoryApproximation where
  U := Set.univ
  root := 0
  root_mem := Set.mem_univ 0
  isOpen := isOpen_univ
  isPreconnected := isPreconnected_univ
  carrier := fkIsingExpandingSquareCarrier
  mesh := fkIsingExpandingSquareMesh
  mesh_pos := fkIsingExpandingSquareMesh_pos
  mesh_tendsto_zero := fkIsingExpandingSquareMesh_tendsto_zero
  compact_eventually_mem := by
    intro K hK _
    exact fkIsingExpandingSquare_compact_eventually_mem K hK
  exterior_eventually_avoided := by
    intro z hz
    simp at hz
  P := fun k ↦ fkIsingSquareBoundaryDeletedPlanar
    (fkIsingExpandingSquareSide k)
  M := fun k ↦ FKIsingSquareWiredCarrier (fkIsingExpandingSquareSide k)
  fintypeM := fun _ ↦ inferInstance
  decEqM := fun _ ↦ inferInstance
  dobrushin := fun k ↦ fkIsingSquareBoundaryPerturbedDobrushinDomain
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertexEmbedding := fun k _ ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) .source
  medialEmbedding := fun k ↦ fkIsingSquareWiredPerturbedCarrierPosition
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  vertex_mem_carrier := by
    intro k v
    refine ⟨.source, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  medial_mem_carrier := by
    intro k a
    refine ⟨a, ?_⟩
    rw [dist_self]
    exact (fkIsingExpandingSquareMesh_pos k).le
  carrier_near_medial := by
    intro k z hz
    exact hz
  medialEmbedding_eq_position := by
    intro k a
    rfl
  rawInterpolant := fun k ↦ fkIsingSquareBoundaryPerturbedHolomorphicInterpolant
    (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
    (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k)
  rawInterpolant_medial := by
    intro k a
    exact fkIsingSquareBoundaryPerturbedHolomorphicInterpolant_medial
      (fkIsingExpandingSquareSide k) (fkIsingExpandingSquareSide_pos k)
      (fkIsingExpandingSquareScale k) (fkIsingExpandingSquareScale_pos k) a

def fkIsingSquareDirectionComplexStep :
    FKIsingSquareDirection → Complex
  | .east => 1
  | .north => Complex.I
  | .west => -1
  | .south => -Complex.I

end
end StatMech.Universality
