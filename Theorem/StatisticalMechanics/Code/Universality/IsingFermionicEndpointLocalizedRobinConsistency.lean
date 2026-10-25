/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointLocalizedRobinConsistency.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRobinCompatibility.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicEndpointLocalizedRobinConsistency


namespace StatMech.Universality

open Finset SimpleGraph Filter Metric Set Topology

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem isingFiniteWeightedLocalizedPoissonBarrier_boundary
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (hx : boundary x) :
    isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
      exceptional hconductance hpositive hhit x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y => if boundary y then 0 else if exceptional y then -1 else 0)) x
  change (if boundary x then
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
          exceptional hconductance hpositive hhit) x) =
    (if boundary x then 0 else if exceptional x then -1 else 0) at h
  simpa [hx] using h

theorem isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (hx : Not (boundary x)) (hxe : exceptional x) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit) x = -1 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y => if boundary y then 0 else if exceptional y then -1 else 0)) x
  change (if boundary x then
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
          exceptional hconductance hpositive hhit) x) =
    (if boundary x then 0 else if exceptional x then -1 else 0) at h
  simpa [hx, hxe] using h

theorem isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (x : V) (hx : Not (boundary x)) (hxe : Not (exceptional x)) :
    isingFiniteWeightedLaplacian conductance
      (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit) x = 0 := by
  classical
  have h := congrFun (isingFiniteWeightedDirichletOperator_solve
    G conductance boundary hconductance hpositive hhit
    (fun y => if boundary y then 0 else if exceptional y then -1 else 0)) x
  change (if boundary x then
      isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
        exceptional hconductance hpositive hhit x else
      isingFiniteWeightedLaplacian conductance
        (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
          exceptional hconductance hpositive hhit) x) =
    (if boundary x then 0 else if exceptional x then -1 else 0) at h
  simpa [hx, hxe] using h

theorem isingFiniteWeightedLocalizedPoissonBarrier_nonneg
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary exceptional : V -> Prop)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
    forall x, 0 <= isingFiniteWeightedLocalizedPoissonBarrier G conductance
      boundary exceptional hconductance hpositive hhit x := by
  apply isingFiniteWeighted_const_le_superharmonic
    G conductance boundary
    (isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary
      exceptional hconductance hpositive hhit) 0
    hconductance hpositive hhit
  · intro x hx
    by_cases hxe : exceptional x
    · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_mem
        G conductance boundary exceptional hconductance hpositive hhit x hx hxe]
      norm_num
    · rw [isingFiniteWeightedLocalizedPoissonBarrier_laplacian_of_not_mem
        G conductance boundary exceptional hconductance hpositive hhit x hx hxe]
  · intro x hx
    rw [isingFiniteWeightedLocalizedPoissonBarrier_boundary
      G conductance boundary exceptional hconductance hpositive hhit x hx]


theorem isingFiniteWeighted_harmonic_approximation_of_endpoint_barriers
    {V : Type*} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) (conductance : V -> V -> Real)
    (boundary layer exceptional : V -> Prop)
    (harmonic target bulkBarrier layerBarrier endpointBarrier : V -> Real)
    (boundaryError bulkResidual layerResidual endpointResidual : Real)
    (hconductance : forall x y, 0 <= conductance x y)
    (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
    (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
    (hharmonic : IsingFiniteWeightedHarmonicOn
      conductance boundary harmonic)
    (hboundary : forall x, boundary x ->
      |harmonic x - target x| <= boundaryError)
    (hbulkResidual : 0 <= bulkResidual)
    (hlayerResidual : 0 <= layerResidual)
    (hendpointResidual : 0 <= endpointResidual)
    (hbulk_nonneg : forall x, 0 <= bulkBarrier x)
    (hlayer_nonneg : forall x, 0 <= layerBarrier x)
    (hendpoint_nonneg : forall x, 0 <= endpointBarrier x)
    (hbulk_laplacian : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance bulkBarrier x <= -1)
    (hlayer_laplacian_nonpos : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= 0)
    (hlayer_laplacian : forall x, Not (boundary x) -> layer x ->
      isingFiniteWeightedLaplacian conductance layerBarrier x <= -1)
    (hendpoint_laplacian_nonpos : forall x, Not (boundary x) ->
      isingFiniteWeightedLaplacian conductance endpointBarrier x <= 0)
    (hendpoint_laplacian : forall x, Not (boundary x) -> exceptional x ->
      isingFiniteWeightedLaplacian conductance endpointBarrier x <= -1)
    (htarget_bulk : forall x, Not (boundary x) -> Not (layer x) ->
      Not (exceptional x) ->
      |isingFiniteWeightedLaplacian conductance target x| <= bulkResidual)
    (htarget_layer : forall x, Not (boundary x) -> layer x ->
      Not (exceptional x) ->
      |isingFiniteWeightedLaplacian conductance target x| <= layerResidual)
    (htarget_endpoint : forall x, Not (boundary x) -> exceptional x ->
      |isingFiniteWeightedLaplacian conductance target x| <= endpointResidual) :
    forall x, |harmonic x - target x| <= boundaryError +
      bulkResidual * bulkBarrier x + layerResidual * layerBarrier x +
        endpointResidual * endpointBarrier x := by
  let upper : V -> Real := fun x =>
    target x + bulkResidual * bulkBarrier x +
      layerResidual * layerBarrier x +
        endpointResidual * endpointBarrier x + boundaryError
  let lower : V -> Real := fun x =>
    target x - bulkResidual * bulkBarrier x -
      layerResidual * layerBarrier x -
        endpointResidual * endpointBarrier x - boundaryError
  have hupper_super :
      IsingFiniteWeightedSuperharmonicOn conductance boundary upper := by
    intro x hx
    rw [show upper = fun y =>
        ((((target y + bulkResidual * bulkBarrier y) +
          layerResidual * layerBarrier y) +
          endpointResidual * endpointBarrier y) + boundaryError) by rfl,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxe : exceptional x
    · have ht := (abs_le.mp (htarget_endpoint x hx hxe)).2
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      have he := hendpoint_laplacian x hx hxe
      nlinarith
    · by_cases hxl : layer x
      · have ht := (abs_le.mp (htarget_layer x hx hxl hxe)).2
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian x hx hxl
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
      · have ht := (abs_le.mp (htarget_bulk x hx hxl hxe)).2
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian_nonpos x hx
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
  have hlower_sub :
      IsingFiniteWeightedSubharmonicOn conductance boundary lower := by
    intro x hx
    rw [show lower = fun y =>
        ((((target y + (-bulkResidual) * bulkBarrier y) +
          (-layerResidual) * layerBarrier y) +
          (-endpointResidual) * endpointBarrier y) + (-boundaryError)) by
          funext y
          dsimp only [lower]
          ring,
      isingFiniteWeightedLaplacian_add_const,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_add,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul,
      isingFiniteWeightedLaplacian_const_mul]
    by_cases hxe : exceptional x
    · have ht := (abs_le.mp (htarget_endpoint x hx hxe)).1
      have hb := hbulk_laplacian x hx
      have hl := hlayer_laplacian_nonpos x hx
      have he := hendpoint_laplacian x hx hxe
      nlinarith
    · by_cases hxl : layer x
      · have ht := (abs_le.mp (htarget_layer x hx hxl hxe)).1
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian x hx hxl
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
      · have ht := (abs_le.mp (htarget_bulk x hx hxl hxe)).1
        have hb := hbulk_laplacian x hx
        have hl := hlayer_laplacian_nonpos x hx
        have he := hendpoint_laplacian_nonpos x hx
        nlinarith
  have hupper : forall x, harmonic x <= upper x := by
    apply isingFiniteWeighted_harmonic_le_superharmonic
      G conductance boundary harmonic upper hconductance hpositive hhit
      hharmonic hupper_super
    intro x hx
    have hb := (abs_le.mp (hboundary x hx)).2
    have hq := hbulk_nonneg x
    have hl := hlayer_nonneg x
    have he := hendpoint_nonneg x
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
    have he := hendpoint_nonneg x
    dsimp only [lower]
    nlinarith
  intro x
  rw [abs_le]
  have hu := hupper x
  have hd := hlower x
  dsimp only [upper] at hu
  dsimp only [lower] at hd
  constructor <;> nlinarith

namespace FKIsingSquareBoundaryLayerCoordinateOneForm


theorem expandingSquare_scaledFourth_factor_eq_one (k : Nat) :
    |fkIsingExpandingSquareScale k| ^ 4 *
        (fkIsingExpandingSquareSide k : Real) ^ 2 = 1 := by
  have hk : (0 : Real) < (k : Real) + 1 := by positivity
  rw [fkIsingExpandingSquareScale, fkIsingExpandingSquareSide]
  push_cast
  rw [abs_of_pos (one_div_pos.mpr hk)]
  field_simp


theorem tendsto_expandingSquare_scaledFourth_of_bound_tendsto
    (derivativeBound : Nat -> Real)
    (hbound : Tendsto derivativeBound atTop (nhds 0)) :
    Tendsto
      (fun k => derivativeBound k *
        |fkIsingExpandingSquareScale k| ^ 4 *
          (fkIsingExpandingSquareSide k : Real) ^ 2)
      atTop (nhds 0) := by
  convert hbound using 1
  funext k
  rw [mul_assoc, expandingSquare_scaledFourth_factor_eq_one, mul_one]


end FKIsingSquareBoundaryLayerCoordinateOneForm
end
end StatMech.Universality
