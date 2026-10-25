/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicBoundaryLayerConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalFullSquareBoundaryLayerDirichletRate.Part6


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingFiniteWeighted_harmonic_approximation_of_layer_barriers
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary layer : V -> Prop)
    (harmonic target bulkBarrier layerBarrier : V -> Real)
    (boundaryError bulkResidual layerResidual bulkBound layerBound : Real)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : forall x, boundary x ->
      |harmonic x - target x| <= boundaryError)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hbulk_nonneg : forall x, 0 <= bulkBarrier x)
    (hlayer_nonneg : forall x, 0 <= layerBarrier x)
    (hbulk_bound : forall x, bulkBarrier x <= bulkBound)
    (hlayer_bound : forall x, layerBarrier x <= layerBound)
    (hbulk_laplacian : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance bulkBarrier x <= -1)
    (hlayer_laplacian_nonpos : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= 0)
    (hlayer_laplacian : forall x, Not (boundary x) -> layer x ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= -1)
    (htarget_bulk : forall x, Not (boundary x) -> Not (layer x) ->
      |isingFiniteWeightedLaplacian conductance target x| <= bulkResidual)
    (htarget_layer : forall x, Not (boundary x) -> layer x ->
      |isingFiniteWeightedLaplacian conductance target x| <= layerResidual) :
    forall x, |harmonic x - target x| <=
      boundaryError + bulkResidual * bulkBound + layerResidual * layerBound := by
  let upper : V -> Real := fun x =>
    target x + bulkResidual * bulkBarrier x +
      layerResidual * layerBarrier x + boundaryError
  let lower : V -> Real := fun x =>
    target x - bulkResidual * bulkBarrier x -
      layerResidual * layerBarrier x - boundaryError
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y =>
        ((target y + bulkResidual * bulkBarrier y) +
          layerResidual * layerBarrier y) + boundaryError by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxl : layer x
    · have ht := (abs_le.mp (htarget_layer x hx hxl)).2
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian x hx hxl
      nlinarith
    · have ht := (abs_le.mp (htarget_bulk x hx hxl)).2
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      nlinarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y =>
        ((target y + (-bulkResidual) * bulkBarrier y) +
          (-layerResidual) * layerBarrier y) + (-boundaryError) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxl : layer x
    · have ht := (abs_le.mp (htarget_layer x hx hxl)).1
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian x hx hxl
      nlinarith
    · have ht := (abs_le.mp (htarget_bulk x hx hxl)).1
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      nlinarith
  have hupper : forall x, harmonic x <= upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hq := hbulk_nonneg x
    have hl := hlayer_nonneg x
    dsimp only [upper]
    nlinarith
  have hlower : forall x, lower x <= harmonic x := by
    apply isingFiniteWeighted_subharmonic_le_harmonic
      G conductance boundary lower harmonic hconductance hpositive hhit
      hlower_sub hharmonic
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).1
    have hq := hbulk_nonneg x
    have hl := hlayer_nonneg x
    dsimp only [lower]
    nlinarith
  intro x
  rw [abs_le]
  have hq := hbulk_bound x
  have hl := hlayer_bound x
  have hu := hupper x
  have hd := hlower x
  dsimp only [upper] at hu
  dsimp only [lower] at hd
  constructor <;> nlinarith

end
end StatMech.Universality
