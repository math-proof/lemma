import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLocalizedPoissonLinearity.Part4
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteWeightedDirichletSolve_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedDirichletSolve_add_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (f g : V -> Real) :
-- imply
  isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit (f + g) = isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit f + isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit g := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedDirichletSolve_add G conductance boundary hconductance hpositive hhit f g

/--
[isingFiniteWeightedDirichletSolve_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedDirichletSolve_smul_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {c : Real}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (f : V -> Real) :
-- imply
  isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit (c • f) = c • isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit f := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedDirichletSolve_smul G conductance boundary hconductance hpositive hhit c f

/--
[isingFiniteWeightedDirichletSolve_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedDirichletSolve_sum_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {s : Finset I}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (f : I -> V -> Real) :
-- imply
  isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit (∑ i ∈ s, f i) = ∑ i ∈ s, isingFiniteWeightedDirichletSolve G conductance boundary hconductance hpositive hhit (f i) := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedDirichletSolve_sum G conductance boundary hconductance hpositive hhit s f

/--
[isingFiniteWeightedLaplacian_pair_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedLaplacian_pair_comm_eq
  [Fintype V]
-- given
  (conductance : V -> V -> Real)
  (hsymm : forall x y, conductance x y = conductance y x)
  (f g : V -> Real) :
-- imply
  (∑ x, f x * isingFiniteWeightedLaplacian conductance g x) = ∑ x, g x * isingFiniteWeightedLaplacian conductance f x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLaplacian_pair_comm conductance hsymm f g

/--
[isingFiniteGhostConductance_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteGhostConductance_comm_eq
  {G : SimpleGraph V}
  {x y : Option V}
-- given
  (ghostRate : V -> Real) :
-- imply
  isingFiniteGhostConductance G ghostRate x y = isingFiniteGhostConductance G ghostRate y x := by
-- proof
  apply StatMech.Universality.isingFiniteGhostConductance_comm G ghostRate x y

/--
[isingFiniteWeightedSpatialResidualPotential_eq_sum_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedSpatialResidualPotential_eq_sum_point_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (residual : V -> Real) :
-- imply
  isingFiniteWeightedSpatialResidualPotential G conductance boundary hconductance hpositive hhit residual = ∑ z ∈ (Finset.univ : Finset V), residual z • isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit z := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedSpatialResidualPotential_eq_sum_point G conductance boundary hconductance hpositive hhit residual

/--
[isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (residual bound : V -> Real)
  (hresidual : forall z, 0 <= residual z)
  (hbound : forall z, isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit z x <= bound z) :
-- imply
  isingFiniteWeightedSpatialResidualPotential G conductance boundary hconductance hpositive hhit residual x <= ∑ z ∈ (Finset.univ : Finset V), residual z * bound z := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedSpatialResidualPotential_le_sum_point_bound G conductance boundary hconductance hpositive hhit residual bound x hresidual hbound

/--
[isingFiniteWeightedPointPoissonBarrier_eq_localized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_eq_localized_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
-- imply
  isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source = isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary (fun x => x = source) hconductance hpositive hhit := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_eq_localized G conductance boundary hconductance hpositive hhit source

/--
[isingFiniteWeightedPointPoissonBarrier_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_boundary_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source x : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hx : boundary x) :
-- imply
  isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_boundary G conductance boundary hconductance hpositive hhit source x hx

/--
[isingFiniteWeightedPointPoissonBarrier_laplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_laplacian_source_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hsource : Not (boundary source)) :
-- imply
  isingFiniteWeightedLaplacian conductance (isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source) source = -1 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_laplacian_source G conductance boundary hconductance hpositive hhit source hsource

/--
[isingFiniteWeightedPointPoissonBarrier_laplacian_off_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_laplacian_off_source_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source x : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hx : Not (boundary x))
  (hxs : x ≠ source) :
-- imply
  isingFiniteWeightedLaplacian conductance (isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source) x = 0 := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_laplacian_off_source G conductance boundary hconductance hpositive hhit source x hx hxs

/--
[isingFiniteWeightedPointPoissonBarrier_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_nonneg_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
-- imply
  forall x, 0 <= isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_nonneg G conductance boundary hconductance hpositive hhit source

/--
[isingFiniteWeightedPointPoissonBarrier_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_comm_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {a b : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hsymm : forall x y, conductance x y = conductance y x)
  (ha : Not (boundary a))
  (hb : Not (boundary b)) :
-- imply
  isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit a b = isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit b a := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_comm G conductance boundary hconductance hpositive hhit hsymm a b ha hb

/--
[isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {source : V}
-- given
  (conductance : V -> V -> Real)
  (boundary : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hsource : Not (boundary source))
  (barrier : V -> Real)
  (hboundary : forall x, boundary x -> 0 <= barrier x)
  (hsourceLap : isingFiniteWeightedLaplacian conductance barrier source <= -1)
  (hoffLap : forall x, Not (boundary x) -> x ≠ source -> isingFiniteWeightedLaplacian conductance barrier x <= 0) :
-- imply
  forall x, isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit source x <= barrier x := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedPointPoissonBarrier_le_of_superharmonic G conductance boundary hconductance hpositive hhit source hsource barrier hboundary hsourceLap hoffLap

/--
[isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b) :
-- imply
  isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit = ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional, isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit z := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_eq_sum_point G conductance boundary exceptional hconductance hpositive hhit

/--
[isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
  {B : Real}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hpoint : forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional -> isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit z x <= B) :
-- imply
  isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit x <= (isingFiniteWeightedInteriorExceptionalSources boundary exceptional).card * B := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul G conductance boundary exceptional hconductance hpositive hhit x B hpoint

/--
[isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal_eq
  [Fintype V]
  [Nonempty V]
  {G : SimpleGraph V}
  {x : V}
  {B : Real}
-- given
  (conductance : V -> V -> Real)
  (boundary exceptional : V -> Prop)
  (hconductance : forall x y, 0 <= conductance x y)
  (hpositive : forall ⦃x y⦄, G.Adj x y -> 0 < conductance x y)
  (hhit : forall x, exists b, boundary b /\ G.Reachable x b)
  (hsymm : forall x y, conductance x y = conductance y x)
  (hx : Not (boundary x))
  (hpoint : forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources boundary exceptional -> isingFiniteWeightedPointPoissonBarrier G conductance boundary hconductance hpositive hhit x z <= B) :
-- imply
  isingFiniteWeightedLocalizedPoissonBarrier G conductance boundary exceptional hconductance hpositive hhit x <= (isingFiniteWeightedInteriorExceptionalSources boundary exceptional).card * B := by
-- proof
  apply StatMech.Universality.isingFiniteWeightedLocalizedPoissonBarrier_le_card_mul_reciprocal G conductance boundary exceptional hconductance hpositive hhit hsymm x hx B hpoint

/--
[vertexMarkedEndpointBarrier_eq_sum_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_eq_sum_point_eq
  {n radius : Nat} :
-- imply
  vertexMarkedEndpointBarrier n radius = ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius), isingFiniteWeightedPointPoissonBarrier (vertexGhostGraph n) (vertexGhostConductance n) (vertexDirichletBoundary n) (vertexGhostConductance_nonneg n) (vertexGhostConductance_pos_of_adj n) (vertexGhost_reaches_boundary n) z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_eq_sum_point n radius

/--
[faceMarkedEndpointBarrier_eq_sum_point](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_eq_sum_point_eq
  {n radius : Nat} :
-- imply
  faceMarkedEndpointBarrier n radius = ∑ z ∈ isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius), isingFiniteWeightedPointPoissonBarrier (faceGhostGraph n) (faceGhostConductance n) (faceDirichletBoundary n) (faceGhostConductance_nonneg n) (faceGhostConductance_pos_of_adj n) (faceGhost_reaches_boundary n) z := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_eq_sum_point n radius

/--
[vertexMarkedEndpointBarrier_le_card_mul_reciprocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma vertexMarkedEndpointBarrier_le_card_mul_reciprocal_eq
  {n radius : Nat}
  {x : Option (FKIsingSquareFullVertexNode n)}
  {B : Real}
-- given
  (hx : Not (vertexDirichletBoundary n x))
  (hpoint : forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) -> vertexPointPoissonBarrier n x z <= B) :
-- imply
  vertexMarkedEndpointBarrier n radius x <= (isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius)).card * B := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointBarrier_le_card_mul_reciprocal n radius x hx B hpoint

/--
[faceMarkedEndpointBarrier_le_card_mul_reciprocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma faceMarkedEndpointBarrier_le_card_mul_reciprocal_eq
  {n radius : Nat}
  {x : Option (FKIsingSquareFullFaceNode n)}
  {B : Real}
-- given
  (hx : Not (faceDirichletBoundary n x))
  (hpoint : forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius) -> facePointPoissonBarrier n x z <= B) :
-- imply
  faceMarkedEndpointBarrier n radius x <= (isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary n) (faceMarkedEndpointLayer n radius)).card * B := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.faceMarkedEndpointBarrier_le_card_mul_reciprocal n radius x hx B hpoint

/--
[PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_of_pointGreen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLocalizedPoissonLinearity.lean)
-/
@[path]
private lemma primitive_convergence_away_of_pointGreen_eq
  {N : Nat -> Nat}
  {hN : forall k, 0 < N k}
  {Phi : Complex -> Complex}
  {mesh : Nat -> Real}
  {radius : Nat -> Nat}
  {bulkRate layerRate endpointRate : Nat -> Real}
  {H : PhysicalEndpointLocalizedRobinInputs N hN Phi mesh radius bulkRate layerRate endpointRate}
-- given
  (safe : forall k, FKIsingSquareInteriorRadialIncidence (N k) (hN k) -> Prop)
  (vertexGreenBound faceGreenBound mismatchRate : Nat -> Real)
  (hvertexGreen_nonneg : forall k, 0 <= vertexGreenBound k)
  (hfaceGreen_nonneg : forall k, 0 <= faceGreenBound k)
  (hmismatch_nonneg : forall k, 0 <= mismatchRate k)
  (hvertexInterior : forall k e, safe k e -> Not (vertexDirichletBoundary (N k) (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))))
  (hfaceInterior : forall k e, safe k e -> Not (faceDirichletBoundary (N k) (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))))
  (hvertexGreen : forall k e, safe k e -> forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary (N k)) (vertexMarkedEndpointLayer (N k) (radius k)) -> vertexPointPoissonBarrier (N k) (some (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e)) z <= vertexGreenBound k)
  (hfaceGreen : forall k e, safe k e -> forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary (N k)) (faceMarkedEndpointLayer (N k) (radius k)) -> facePointPoissonBarrier (N k) (some (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e)) z <= faceGreenBound k)
  (hmismatch : forall k e, safe k e -> |(Phi (fullSquareScaledFaceEmbedding (N k) (mesh k) (fkIsingSquareFullFaceOfRadialIncidence (N k) (hN k) e))).im - (Phi (fullSquareScaledVertexEmbedding (N k) (mesh k) (fkIsingSquareInteriorRadialEndpoint (N k) (hN k) e))).im| <= mismatchRate k)
  (hvertexEndpoint_tendsto : Filter.Tendsto (fun k => endpointRate k * ((isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary (N k)) (vertexMarkedEndpointLayer (N k) (radius k))).card * vertexGreenBound k)) Filter.atTop (nhds 0))
  (hfaceEndpoint_tendsto : Filter.Tendsto (fun k => endpointRate k * ((isingFiniteWeightedInteriorExceptionalSources (faceDirichletBoundary (N k)) (faceMarkedEndpointLayer (N k) (radius k))).card * faceGreenBound k)) Filter.atTop (nhds 0))
  (hmismatch_tendsto : Filter.Tendsto mismatchRate Filter.atTop (nhds 0)) :
-- imply
  forall eta : Real, 0 < eta -> ∀ᶠ k in Filter.atTop, forall e : FKIsingSquareInteriorRadialIncidence (N k) (hN k), safe k e -> := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.PhysicalEndpointLocalizedRobinInputs.primitive_convergence_away_of_pointGreen H safe vertexGreenBound faceGreenBound mismatchRate hvertexGreen_nonneg hfaceGreen_nonneg hmismatch_nonneg hvertexInterior hfaceInterior hvertexGreen hfaceGreen hmismatch hvertexEndpoint_tendsto hfaceEndpoint_tendsto hmismatch_tendsto


-- created on 2026-10-23
