/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicScalingReduction
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalDirichletLimit.Part2
open Filter Set Topology Metric


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.BeffaraDC

noncomputable section

structure FKIsingCaratheodoryApproximation where
  U : Set Complex
  root : Complex
  root_mem : root ∈ U
  isOpen : IsOpen U
  isPreconnected : IsPreconnected U
  carrier : Nat → Set Complex
  mesh : Nat → Real
  mesh_pos : ∀ n, 0 < mesh n
  mesh_tendsto_zero : Tendsto mesh atTop (nhds 0)
  compact_eventually_mem : ∀ K : Set Complex,
    IsCompact K → K ⊆ U → ∀ᶠ n in atTop, K ⊆ carrier n
  exterior_eventually_avoided : ∀ z ∉ closure U,
    ∃ r : Real, 0 < r ∧
      ∀ᶠ n in atTop, Disjoint (ball z r) (carrier n)
  P : Nat → PlanarZ2Subgraph
  M : Nat → Type
  fintypeM : ∀ n, Fintype (M n)
  decEqM : ∀ n, DecidableEq (M n)
  dobrushin : ∀ n, FKIsingDobrushinDomain (P n) (M n)
  vertexEmbedding : ∀ n, (P n).V → Complex
  medialEmbedding : ∀ n, M n → Complex
  vertex_mem_carrier : ∀ n v, vertexEmbedding n v ∈ carrier n
  medial_mem_carrier : ∀ n e, medialEmbedding n e ∈ carrier n
  carrier_near_medial : ∀ n z, z ∈ carrier n →
    ∃ e : M n, dist z (medialEmbedding n e) ≤ mesh n
  medialEmbedding_eq_position : ∀ n e,
    medialEmbedding n e = (dobrushin n).medialPosition e
  rawInterpolant : Nat → Complex → Complex
  rawInterpolant_medial : ∀ n e,
    rawInterpolant n (medialEmbedding n e) =
      @FKIsingDobrushinDomain.fermionicObservable
        (P n) (M n) (decEqM n) (dobrushin n) e

end
end StatMech.Universality
