import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
open StatMech StatMech.FrontierA


/--
[typedTrueEndpoint_spin_eq_true_of_mem_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedTrueEndpoint_spin_eq_true_of_mem_cut_eq
  [Fintype P]
  [DecidableEq P]
  {p : P}
-- given
  (ends : P -> V × V)
  (chi : V -> Bool)
  (hp : p ∈ multibondCut ends chi) :
-- imply
  chi (typedTrueEndpoint ends chi p) = true := by
-- proof
  apply StatMech.FrontierA.typedTrueEndpoint_spin_eq_true_of_mem_cut ends chi p hp

/--
[typedFalseEndpoint_spin_eq_false_of_mem_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFalseEndpoint_spin_eq_false_of_mem_cut_eq
  [Fintype P]
  [DecidableEq P]
  {p : P}
-- given
  (ends : P -> V × V)
  (chi : V -> Bool)
  (hp : p ∈ multibondCut ends chi) :
-- imply
  chi (typedFalseEndpoint ends chi p) = false := by
-- proof
  apply StatMech.FrontierA.typedFalseEndpoint_spin_eq_false_of_mem_cut ends chi p hp

/--
[typedMarkedOppositeSides_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedMarkedOppositeSides_disjoint_eq
  [Fintype P]
  [DecidableEq P]
  {B₁ B₂ : Finset P}
-- given
  (ends : P -> V × V)
  (chi : V -> Bool)
  (hB₁ : B₁ ⊆ multibondCut ends chi)
  (hB₂ : B₂ ⊆ multibondCut ends chi) :
-- imply
  Disjoint (typedMarkedBondVertices (typedTrueEndpoint ends chi) B₁) (typedMarkedBondVertices (typedFalseEndpoint ends chi) B₂) := by
-- proof
  apply StatMech.FrontierA.typedMarkedOppositeSides_disjoint ends chi B₁ B₂ hB₁ hB₂

/--
[typedBondEndpointDisconnections_subset_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedBondEndpointDisconnections_subset_consistency_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (hends : forall p, (ends p).1 ≠ (ends p).2) :
-- imply
  finiteEventInter ((typedBondFirstEndpoints ends D).product (typedBondSecondEndpoints ends D)) (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆ typedFKConsistencyEvent ends D := by
-- proof
  apply StatMech.FrontierA.typedBondEndpointDisconnections_subset_consistency ends hends D

/--
[typedTwoCutCoveredDisconnections_subset_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedTwoCutCoveredDisconnections_subset_consistency_eq
  [Fintype P]
  [DecidableEq P]
  {D B₁ B₂ : Finset P}
  {U₁ U₂ : Finset V}
-- given
  (ends : P -> V × V)
  (hends : forall p, (ends p).1 ≠ (ends p).2)
  (hcover₁ : forall p, p ∈ B₁ -> (ends p).1 ∈ U₁ ∨ (ends p).2 ∈ U₁)
  (hcover₂ : forall p, p ∈ B₂ -> (ends p).1 ∈ U₂ ∨ (ends p).2 ∈ U₂)
  (tau chi : V -> Bool)
  (hshift : multibondCut ends tau = D ∆ B₁)
  (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
-- imply
  finiteEventInter (U₁.product U₂) (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆ typedFKConsistencyEvent ends D := by
-- proof
  apply StatMech.FrontierA.typedTwoCutCoveredDisconnections_subset_consistency ends hends D B₁ B₂ U₁ U₂ hcover₁ hcover₂ tau chi hshift hboundary

/--
[typedTwoCutDisconnections_subset_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedTwoCutDisconnections_subset_consistency_eq
  [Fintype P]
  [DecidableEq P]
  {D B₁ B₂ : Finset P}
-- given
  (ends : P -> V × V)
  (hends : forall p, (ends p).1 ≠ (ends p).2)
  (tau chi : V -> Bool)
  (hshift : multibondCut ends tau = D ∆ B₁)
  (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
-- imply
  finiteEventInter ((typedBondVertices ends B₁).product (typedBondVertices ends B₂)) (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆ typedFKConsistencyEvent ends D := by
-- proof
  apply StatMech.FrontierA.typedTwoCutDisconnections_subset_consistency ends hends D B₁ B₂ tau chi hshift hboundary

/--
[typedTwoCutMarkedDisconnections_subset_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedTwoCutMarkedDisconnections_subset_consistency_eq
  [Fintype P]
  [DecidableEq P]
  {D B₁ B₂ : Finset P}
-- given
  (ends : P -> V × V)
  (hends : forall p, (ends p).1 ≠ (ends p).2)
  (tau chi : V -> Bool)
  (hshift : multibondCut ends tau = D ∆ B₁)
  (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
-- imply
  finiteEventInter ((typedMarkedBondVertices (typedTrueEndpoint ends chi) B₁).product (typedMarkedBondVertices (typedFalseEndpoint ends chi) B₂)) (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆ typedFKConsistencyEvent ends D := by
-- proof
  apply StatMech.FrontierA.typedTwoCutMarkedDisconnections_subset_consistency ends hends D B₁ B₂ tau chi hshift hboundary

/--
[typedFKEventMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFKEventMass_nonneg_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (A : Set (P -> Bool)) :
-- imply
  0 <= typedFKEventMass ends rho A := by
-- proof
  apply StatMech.FrontierA.typedFKEventMass_nonneg ends hrho0 hrho1 hZ A

/--
[typedFKEventMass_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFKEventMass_mono_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {A B : Set (P -> Bool)}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (hAB : A ⊆ B) :
-- imply
  typedFKEventMass ends rho A <= typedFKEventMass ends rho B := by
-- proof
  apply StatMech.FrontierA.typedFKEventMass_mono ends hrho0 hrho1 hZ hAB

/--
[typedFKEventMass_disconn_eq_one_sub_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFKEventMass_disconn_eq_one_sub_twoPoint_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (hZ : typedFKZ ends rho ≠ 0) :
-- imply
  typedFKEventMass ends rho (typedFKDisconnEvent ends x y) = 1 - typedFKTwoPoint ends rho x y := by
-- proof
  apply StatMech.FrontierA.typedFKEventMass_disconn_eq_one_sub_twoPoint ends rho hZ x y

/--
[typedFK_finite_pair_nonconnection_product_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFK_finite_pair_nonconnection_product_bound_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {upper lower : Finset V}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho) :
-- imply
  (∏ uv ∈ upper.product lower, (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <= typedFKEventMass ends rho (finiteEventInter (upper.product lower) (fun uv => typedFKDisconnEvent ends uv.1 uv.2)) := by
-- proof
  apply StatMech.FrontierA.typedFK_finite_pair_nonconnection_product_bound ends hrho0 hrho1 hZ upper lower

/--
[typedFK_consistencyMass_ge_pair_nonconnection_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFK_consistencyMass_ge_pair_nonconnection_product_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {D : Finset P}
  {upper lower : Finset V}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (hgeometry : finiteEventInter (upper.product lower) (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆ typedFKConsistencyEvent ends D) :
-- imply
  (∏ uv ∈ upper.product lower, (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <= typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
-- proof
  apply StatMech.FrontierA.typedFK_consistencyMass_ge_pair_nonconnection_product ends hrho0 hrho1 hZ D upper lower hgeometry

/--
[typedFK_consistencyMass_ge_bondEndpoint_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFK_consistencyMass_ge_bondEndpoint_product_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (hends : forall p, (ends p).1 ≠ (ends p).2)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho) :
-- imply
  (∏ uv ∈ (typedBondFirstEndpoints ends D).product (typedBondSecondEndpoints ends D), (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <= typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
-- proof
  apply StatMech.FrontierA.typedFK_consistencyMass_ge_bondEndpoint_product ends hends hrho0 hrho1 hZ D

/--
[typedFK_consistencyMass_ge_twoCut_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma typedFK_consistencyMass_ge_twoCut_product_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {D B₁ B₂ : Finset P}
-- given
  (ends : P -> V × V)
  (hends : forall p, (ends p).1 ≠ (ends p).2)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (tau chi : V -> Bool)
  (hshift : multibondCut ends tau = D ∆ B₁)
  (hboundary : multibondCut ends chi = B₁ ∪ B₂) :
-- imply
  (∏ uv ∈ (typedBondVertices ends B₁).product (typedBondVertices ends B₂), (1 - typedFKTwoPoint ends rho uv.1 uv.2)) <= typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
-- proof
  apply StatMech.FrontierA.typedFK_consistencyMass_ge_twoCut_product ends hends hrho0 hrho1 hZ D B₁ B₂ tau chi hshift hboundary

/--
[multibondIsing_twist_ratio_ge_pair_correlation_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma multibondIsing_twist_ratio_ge_pair_correlation_product_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
  {upper lower : Finset V}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (hJ : forall p, 0 <= J p)
  (hgeometry : finiteEventInter (upper.product lower) (fun uv => typedFKDisconnEvent ends uv.1 uv.2) ⊆ typedFKConsistencyEvent ends D) :
-- imply
  (∏ uv ∈ upper.product lower, (1 - multibondIsingTwoPoint ends J uv.1 uv.2)) <= multibondIsingPartition ends (multibondTwistCoupling J D) / multibondIsingPartition ends J := by
-- proof
  apply StatMech.FrontierA.multibondIsing_twist_ratio_ge_pair_correlation_product ends J hJ D upper lower hgeometry

/--
[multibondIsingTwoPoint_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma multibondIsingTwoPoint_nonneg_of_nonneg_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (hJ : forall p, 0 <= J p) :
-- imply
  0 <= multibondIsingTwoPoint ends J x y := by
-- proof
  apply StatMech.FrontierA.multibondIsingTwoPoint_nonneg_of_nonneg ends J hJ x y

/--
[multibondIsingTwoPoint_le_one_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma multibondIsingTwoPoint_le_one_of_nonneg_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (hJ : forall p, 0 <= J p) :
-- imply
  multibondIsingTwoPoint ends J x y <= 1 := by
-- proof
  apply StatMech.FrontierA.multibondIsingTwoPoint_le_one_of_nonneg ends J hJ x y

/--
[cubicalXYWilsonExpectation_ge_pair_correlation_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_ge_pair_correlation_product_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {upper lower : Finset (CubicalDualVertex a b c)}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (K : CubicalPlaquette a b c -> Real)
  (hK : forall p, 0 < K p)
  (hgeometry : finiteEventInter (upper.product lower) (fun uv => typedFKDisconnEvent cubicalDualEnds uv.1 uv.2) ⊆ typedFKConsistencyEvent cubicalDualEnds (cubicalXYSheet k)) :
-- imply
  (∏ uv ∈ upper.product lower, (1 - multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_ge_pair_correlation_product ha hb hc k K hK upper lower hgeometry

/--
[cubicalXYSheet_subset_belowCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYSheet_subset_belowCut_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (hk : 0 < k.val) :
-- imply
  cubicalXYSheet (a := a) (b := b) k ⊆ multibondCut (cubicalDualEnds (a := a) (b := b) (c := c)) (cubicalBelowSpin (a := a) (b := b) k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheet_subset_belowCut k hk

/--
[belowCut_eq_sheet_union_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma belowCut_eq_sheet_union_complement_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (hk : 0 < k.val) :
-- imply
  multibondCut (cubicalDualEnds (a := a) (b := b) (c := c)) (cubicalBelowSpin (a := a) (b := b) k) = cubicalXYSheet (a := a) (b := b) k ∪ cubicalLowerComplementSurface (a := a) (b := b) k := by
-- proof
  apply StatMech.FrontierA.belowCut_eq_sheet_union_complement k hk

/--
[belowCut_eq_sheet_symmDiff_complement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma belowCut_eq_sheet_symmDiff_complement_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (hk : 0 < k.val) :
-- imply
  multibondCut (cubicalDualEnds (a := a) (b := b) (c := c)) (cubicalBelowSpin (a := a) (b := b) k) = cubicalXYSheet (a := a) (b := b) k ∆ cubicalLowerComplementSurface (a := a) (b := b) k := by
-- proof
  apply StatMech.FrontierA.belowCut_eq_sheet_symmDiff_complement k hk

/--
[cubicalLowerMarkedSurfaces_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalLowerMarkedSurfaces_disjoint_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (hk : 0 < k.val) :
-- imply
  Disjoint (cubicalLowerComplementInnerVertices (a := a) (b := b) k) (cubicalXYSheetUpperVertices (a := a) (b := b) k) := by
-- proof
  apply StatMech.FrontierA.cubicalLowerMarkedSurfaces_disjoint k hk

/--
[cubicalLowerSlab_pair_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalLowerSlab_pair_ne_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {uv : CubicalDualVertex a b c × CubicalDualVertex a b c}
-- given
  (hk : 0 < k.val)
  (huv : uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k)) :
-- imply
  uv.1 ≠ uv.2 := by
-- proof
  apply StatMech.FrontierA.cubicalLowerSlab_pair_ne k hk uv huv

/--
[cubicalXYSheetUpperVertices_eq_layer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYSheetUpperVertices_eq_layer_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (hk : 0 < k.val)
  (hkTop : k.val < c) :
-- imply
  cubicalXYSheetUpperVertices (a := a) (b := b) k = (Finset.univ : Finset (Fin a × Fin b)).image (fun ij => some (CubicalCell.mk ij.1 ij.2 ⟨k.val, hkTop⟩)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYSheetUpperVertices_eq_layer k hk hkTop

/--
[cubicalLowerSlabDisconnections_subset_consistency](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalLowerSlabDisconnections_subset_consistency_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hk : 0 < k.val) :
-- imply
  finiteEventInter ((cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k)) (fun uv => typedFKDisconnEvent (cubicalDualEnds (a := a) (b := b) (c := c)) uv.1 uv.2) ⊆ typedFKConsistencyEvent (cubicalDualEnds (a := a) (b := b) (c := c)) (cubicalXYSheet (a := a) (b := b) k) := by
-- proof
  apply StatMech.FrontierA.cubicalLowerSlabDisconnections_subset_consistency ha hb hc k hk

/--
[cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hk : 0 < k.val)
  (K : CubicalPlaquette a b c -> Real)
  (hK : forall p, 0 < K p) :
-- imply
  (∏ uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k), (1 - multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_ge_lowerSlab_correlation_product ha hb hc k hk K hK

/--
[cubicalXYWilson_perimeterLower_of_lowerSlab_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYWilson_perimeterLower_of_lowerSlab_sum_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {R C perimeter : Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hk : 0 < k.val)
  (K : CubicalPlaquette a b c -> Real)
  (hK : forall p, 0 < K p)
  (hR0 : 0 < R)
  (hR1 : R < 1)
  (hR : forall uv, uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k) -> multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= R)
  (hsum : (∑ uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k), multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <= C * perimeter) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilson_perimeterLower_of_lowerSlab_sum ha hb hc k hk K hK hR0 hR1 hR hsum

/--
[cubicalXYWilson_perimeterLower_of_lowerSlab_exponential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYWilson_perimeterLower_of_lowerSlab_exponential_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {decay C perimeter : Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (hk : 0 < k.val)
  (K : CubicalPlaquette a b c -> Real)
  (hK : forall p, 0 < K p)
  (hdecay : 0 < decay)
  (separation : CubicalDualVertex a b c × CubicalDualVertex a b c -> Real)
  (hsep : forall uv, uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k) -> 1 <= separation uv)
  (hcorr : forall uv, uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k) -> multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= Real.exp (-decay * separation uv))
  (hsumExp : (∑ uv ∈ (cubicalLowerComplementInnerVertices (a := a) (b := b) k).product (cubicalXYSheetUpperVertices (a := a) (b := b) k), Real.exp (-decay * separation uv)) <= C * perimeter) :
-- imply
  Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * C) * perimeter) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilson_perimeterLower_of_lowerSlab_exponential ha hb hc k hk K hK decay C perimeter hdecay separation hsep hcorr hsumExp

/--
[cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (K : CubicalPlaquette a b c -> Real)
  (hK : forall p, 0 < K p) :
-- imply
  (∏ uv ∈ (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)), (1 - multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2)) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_ge_sheetEndpoint_correlation_product ha hb hc k K hK

/--
[cubicalXYWilson_perimeterLower_of_sheetEndpoint_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinder.lean)
-/
@[path]
private lemma cubicalXYWilson_perimeterLower_of_sheetEndpoint_sum_eq
  [Fintype P]
  [DecidableEq P]
  {a b c : Nat}
  {k : Fin (c + 1)}
  {R C perimeter : Real}
-- given
  (ha : 0 < a)
  (hb : 0 < b)
  (hc : 0 < c)
  (K : CubicalPlaquette a b c -> Real)
  (hK : forall p, 0 < K p)
  (hR0 : 0 < R)
  (hR1 : R < 1)
  (hR : forall uv, uv ∈ (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)) -> multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2 <= R)
  (hsum : (∑ uv ∈ (typedBondFirstEndpoints cubicalDualEnds (cubicalXYSheet k)).product (typedBondSecondEndpoints cubicalDualEnds (cubicalXYSheet k)), multibondIsingTwoPoint cubicalDualEnds (fun p => gaugeDualCoupling (K p)) uv.1 uv.2) <= C * perimeter) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilson_perimeterLower_of_sheetEndpoint_sum ha hb hc k K hK hR0 hR1 hR hsum


-- created on 2026-10-23
