import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK
open StatMech StatMech.FrontierA


/--
[typedESWeight_sum_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_sum_omega_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (sigma : V -> Bool) :
-- imply
  (∑ omega : P -> Bool, typedESWeight ends rho D sigma omega) = ∏ p : P, ∑ b : Bool, typedESEdgeFactor ends rho D sigma p b := by
-- proof
  apply StatMech.FrontierA.typedESWeight_sum_omega ends rho D sigma

/--
[typedESEdgeFactor_sum_bool](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESEdgeFactor_sum_bool_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
  {p : P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (sigma : V -> Bool) :
-- imply
  (∑ b : Bool, typedESEdgeFactor ends rho D sigma p b) = if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1 else 1 - rho p := by
-- proof
  apply StatMech.FrontierA.typedESEdgeFactor_sum_bool ends rho D sigma p

/--
[typedESWeight_sum_omega_eq_shiftedCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_sum_omega_eq_shiftedCut_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (sigma : V -> Bool) :
-- imply
  (∑ omega : P -> Bool, typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) D sigma omega) = ∏ p ∈ multibondCut ends sigma ∆ D, Real.exp (-2 * J p) := by
-- proof
  apply StatMech.FrontierA.typedESWeight_sum_omega_eq_shiftedCut ends J D sigma

/--
[multibondIsingPartition_twist_eq_exp_mul_typedESZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma multibondIsingPartition_twist_eq_exp_mul_typedESZ_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  multibondIsingPartition ends (multibondTwistCoupling J D) = Real.exp (∑ p : P, J p) * typedESZ ends (fun p => 1 - Real.exp (-2 * J p)) D := by
-- proof
  apply StatMech.FrontierA.multibondIsingPartition_twist_eq_exp_mul_typedESZ ends J D

/--
[typedESWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_factor_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (sigma : V -> Bool)
  (omega : P -> Bool) :
-- imply
  typedESWeight ends rho D sigma omega = typedESActivity rho omega * (if TypedSignedCompatible ends D omega sigma then 1 else 0) := by
-- proof
  apply StatMech.FrontierA.typedESWeight_factor ends rho D sigma omega

/--
[bool_xor_eq_xor_iff_eq_iff_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma bool_xor_eq_xor_iff_eq_iff_eq_eq
  [Fintype P]
  [DecidableEq P]
  {a b c d : Bool} :
-- imply
  (a.xor c = b.xor d) <-> ((a = b) <-> (c = d)) := by
-- proof
  apply StatMech.FrontierA.bool_xor_eq_xor_iff_eq_iff_eq a b c d

/--
[typedSpinXor_cancel_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedSpinXor_cancel_right_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (sigma tau : V -> Bool) :
-- imply
  typedSpinXor (typedSpinXor sigma tau) tau = sigma := by
-- proof
  apply StatMech.FrontierA.typedSpinXor_cancel_right sigma tau

/--
[typedESWeight_sum_sigma_eq_activity_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_sum_sigma_eq_activity_mul_card_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (omega : P -> Bool) :
-- imply
  (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) = typedESActivity rho omega * ((Finset.univ.filter (TypedSignedCompatible ends D omega)).card : Real) := by
-- proof
  apply StatMech.FrontierA.typedESWeight_sum_sigma_eq_activity_mul_card ends rho D omega

/--
[typedESWeight_sum_sigma_signed_eq_ordinary_of_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_sum_sigma_signed_eq_ordinary_of_witness_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (omega : P -> Bool)
  (witness : V -> Bool)
  (hw : TypedSignedCompatible ends D omega witness) :
-- imply
  (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) = ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega := by
-- proof
  apply StatMech.FrontierA.typedESWeight_sum_sigma_signed_eq_ordinary_of_witness ends rho D omega witness hw

/--
[typedESWeight_sum_sigma_signed_eq_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_sum_sigma_signed_eq_indicator_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (omega : P -> Bool) :
-- imply
  (∑ sigma : V -> Bool, typedESWeight ends rho D sigma omega) = if omega ∈ typedFKConsistencyEvent ends D then ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega else 0 := by
-- proof
  apply StatMech.FrontierA.typedESWeight_sum_sigma_signed_eq_indicator ends rho D omega

/--
[typedFKZ_eq_typedESZ_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKZ_eq_typedESZ_empty_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (rho : P -> Real) :
-- imply
  typedFKZ ends rho = typedESZ ends rho ∅ := by
-- proof
  apply StatMech.FrontierA.typedFKZ_eq_typedESZ_empty ends rho

/--
[typedESZ_eq_typedFKWeight_filter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESZ_eq_typedFKWeight_filter_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real) :
-- imply
  typedESZ ends rho D = ∑ omega : P -> Bool, typedFKWeight ends rho omega * (typedFKConsistencyEvent ends D).indicator (fun _ => (1 : Real)) omega := by
-- proof
  apply StatMech.FrontierA.typedESZ_eq_typedFKWeight_filter ends rho D

/--
[typedFKZ_pos_of_coupling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKZ_pos_of_coupling_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  0 < typedFKZ ends (fun p => 1 - Real.exp (-2 * J p)) := by
-- proof
  apply StatMech.FrontierA.typedFKZ_pos_of_coupling ends J

/--
[typedFKProb_nonneg_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKProb_nonneg_of_nonneg_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (omega : P -> Bool) :
-- imply
  0 <= typedFKProb ends rho omega := by
-- proof
  apply StatMech.FrontierA.typedFKProb_nonneg_of_nonneg ends hrho0 hrho1 hZ omega

/--
[typedFKProb_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKProb_sum_eq_one_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (hZ : typedFKZ ends rho ≠ 0) :
-- imply
  (∑ omega : P -> Bool, typedFKProb ends rho omega) = 1 := by
-- proof
  apply StatMech.FrontierA.typedFKProb_sum_eq_one ends rho hZ

/--
[typedESZ_div_eq_consistencyMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESZ_div_eq_consistencyMass_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (rho : P -> Real) :
-- imply
  typedESZ ends rho D / typedESZ ends rho ∅ = typedFKEventMass ends rho (typedFKConsistencyEvent ends D) := by
-- proof
  apply StatMech.FrontierA.typedESZ_div_eq_consistencyMass ends rho D

/--
[multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  multibondIsingPartition ends (multibondTwistCoupling J D) / multibondIsingPartition ends J = typedFKEventMass ends (fun p => 1 - Real.exp (-2 * J p)) (typedFKConsistencyEvent ends D) := by
-- proof
  apply StatMech.FrontierA.multibondIsing_twist_partition_ratio_eq_typedFKConsistencyMass ends J D

/--
[cubicalXYWilsonExpectation_eq_typedFKConsistencyMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma cubicalXYWilsonExpectation_eq_typedFKConsistencyMass_eq
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
  gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) = typedFKEventMass cubicalDualEnds (fun p => 1 - Real.exp (-2 * gaugeDualCoupling (K p))) (typedFKConsistencyEvent cubicalDualEnds (cubicalXYSheet k)) := by
-- proof
  apply StatMech.FrontierA.cubicalXYWilsonExpectation_eq_typedFKConsistencyMass ha hb hc k K hK

/--
[typedOpenGraph_sup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedOpenGraph_sup_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (a b : P -> Bool) :
-- imply
  typedOpenGraph ends (a ⊔ b) = typedOpenGraph ends a ⊔ typedOpenGraph ends b := by
-- proof
  apply StatMech.FrontierA.typedOpenGraph_sup ends a b

/--
[typedOpenGraph_inf_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedOpenGraph_inf_le_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (a b : P -> Bool) :
-- imply
  typedOpenGraph ends (a ⊓ b) <= typedOpenGraph ends a ⊓ typedOpenGraph ends b := by
-- proof
  apply StatMech.FrontierA.typedOpenGraph_inf_le ends a b

/--
[typedNumClusters_supermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedNumClusters_supermodular_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (a b : P -> Bool) :
-- imply
  typedNumClusters ends a + typedNumClusters ends b <= typedNumClusters ends (a ⊔ b) + typedNumClusters ends (a ⊓ b) := by
-- proof
  apply StatMech.FrontierA.typedNumClusters_supermodular ends a b

/--
[typedSignedCompatible_empty_iff_graphConstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedSignedCompatible_empty_iff_graphConstant_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (omega : P -> Bool)
  (sigma : V -> Bool) :
-- imply
  TypedSignedCompatible ends ∅ omega sigma <-> forall x y, (typedOpenGraph ends omega).Adj x y -> sigma x = sigma y := by
-- proof
  apply StatMech.FrontierA.typedSignedCompatible_empty_iff_graphConstant ends omega sigma

/--
[card_typedSignedCompatible_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma card_typedSignedCompatible_empty_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (omega : P -> Bool) :
-- imply
  Nat.card {sigma : V -> Bool // TypedSignedCompatible ends ∅ omega sigma} = 2 ^ typedNumClusters ends omega := by
-- proof
  apply StatMech.FrontierA.card_typedSignedCompatible_empty ends omega

/--
[typedFKWeight_eq_activity_mul_clusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKWeight_eq_activity_mul_clusters_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (omega : P -> Bool) :
-- imply
  typedFKWeight ends rho omega = typedESActivity rho omega * (2 : Real) ^ typedNumClusters ends omega := by
-- proof
  apply StatMech.FrontierA.typedFKWeight_eq_activity_mul_clusters ends rho omega

/--
[typedESActivity_logModular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESActivity_logModular_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (rho : P -> Real)
  (a b : P -> Bool) :
-- imply
  typedESActivity rho a * typedESActivity rho b = typedESActivity rho (a ⊔ b) * typedESActivity rho (a ⊓ b) := by
-- proof
  apply StatMech.FrontierA.typedESActivity_logModular rho a b

/--
[typedFKWeight_logSupermodular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKWeight_logSupermodular_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (a b : P -> Bool) :
-- imply
  typedFKWeight ends rho a * typedFKWeight ends rho b <= typedFKWeight ends rho (a ⊔ b) * typedFKWeight ends rho (a ⊓ b) := by
-- proof
  apply StatMech.FrontierA.typedFKWeight_logSupermodular ends hrho0 hrho1 a b

/--
[typedFKProb_FKGLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKProb_FKGLatticeCondition_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho) :
-- imply
  FKGLatticeCondition (typedFKProb ends rho) := by
-- proof
  apply StatMech.FrontierA.typedFKProb_FKGLatticeCondition ends hrho0 hrho1 hZ

/--
[typedFKProb_positively_associated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKProb_positively_associated_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {f g : (P -> Bool) -> Real}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (hf : Monotone f)
  (hg : Monotone g) :
-- imply
  (∑ omega, typedFKProb ends rho omega * f omega) * (∑ omega, typedFKProb ends rho omega * g omega) <= ∑ omega, typedFKProb ends rho omega * (f omega * g omega) := by
-- proof
  apply StatMech.FrontierA.typedFKProb_positively_associated ends hrho0 hrho1 hZ hf hg

/--
[typedFKProb_positively_associated_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKProb_positively_associated_events_eq
  [Fintype P]
  [DecidableEq P]
  {rho : P -> Real}
  {A B : Set (P -> Bool)}
-- given
  (ends : P -> V × V)
  (hrho0 : forall p, 0 <= rho p)
  (hrho1 : forall p, rho p <= 1)
  (hZ : 0 < typedFKZ ends rho)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  typedFKEventMass ends rho A * typedFKEventMass ends rho B <= typedFKEventMass ends rho (A ∩ B) := by
-- proof
  apply StatMech.FrontierA.typedFKProb_positively_associated_events ends hrho0 hrho1 hZ hA hB

/--
[typedOpenGraph_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedOpenGraph_mono_eq
  [Fintype P]
  [DecidableEq P]
  {a b : P -> Bool}
-- given
  (ends : P -> V × V)
  (hab : a <= b) :
-- imply
  typedOpenGraph ends a <= typedOpenGraph ends b := by
-- proof
  apply StatMech.FrontierA.typedOpenGraph_mono ends hab

/--
[typedFKConnEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKConnEvent_isIncreasing_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V) :
-- imply
  IsIncreasing (typedFKConnEvent ends x y) := by
-- proof
  apply StatMech.FrontierA.typedFKConnEvent_isIncreasing ends x y

/--
[typedFKDisconnEvent_isDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKDisconnEvent_isDecreasing_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V) :
-- imply
  IsDecreasing (typedFKDisconnEvent ends x y) := by
-- proof
  apply StatMech.FrontierA.typedFKDisconnEvent_isDecreasing ends x y

/--
[typedSignedCompatible_empty_eq_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedSignedCompatible_empty_eq_of_reachable_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (omega : P -> Bool)
  (sigma : V -> Bool)
  (hsigma : TypedSignedCompatible ends ∅ omega sigma)
  (hxy : (typedOpenGraph ends omega).Reachable x y) :
-- imply
  sigma x = sigma y := by
-- proof
  apply StatMech.FrontierA.typedSignedCompatible_empty_eq_of_reachable ends omega sigma hsigma hxy

/--
[typedReachabilitySpin_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedReachabilitySpin_compatible_eq
  [Fintype P]
  [DecidableEq P]
  {x : V}
-- given
  (ends : P -> V × V)
  (omega : P -> Bool) :
-- imply
  TypedSignedCompatible ends ∅ omega (typedReachabilitySpin ends omega x) := by
-- proof
  apply StatMech.FrontierA.typedReachabilitySpin_compatible ends omega x

/--
[typedSignedCompatible_empty_xor_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedSignedCompatible_empty_xor_iff_eq
  [Fintype P]
  [DecidableEq P]
-- given
  (ends : P -> V × V)
  (omega : P -> Bool)
  (sigma tau : V -> Bool)
  (htau : TypedSignedCompatible ends ∅ omega tau) :
-- imply
  TypedSignedCompatible ends ∅ omega (typedSpinXor sigma tau) <-> TypedSignedCompatible ends ∅ omega sigma := by
-- proof
  apply StatMech.FrontierA.typedSignedCompatible_empty_xor_iff ends omega sigma tau htau

/--
[typedSignedCompatible_xor_iff_symmDiff_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedSignedCompatible_xor_iff_symmDiff_cut_eq
  [Fintype P]
  [DecidableEq P]
  {D : Finset P}
-- given
  (ends : P -> V × V)
  (omega : P -> Bool)
  (sigma tau : V -> Bool) :
-- imply
  TypedSignedCompatible ends D omega (typedSpinXor sigma tau) <-> TypedSignedCompatible ends (D ∆ multibondCut ends tau) omega sigma := by
-- proof
  apply StatMech.FrontierA.typedSignedCompatible_xor_iff_symmDiff_cut ends D omega sigma tau

/--
[typedSpinProduct_xor_reachability_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedSpinProduct_xor_reachability_of_not_reachable_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (omega : P -> Bool)
  (sigma : V -> Bool)
  (hxy : ¬ (typedOpenGraph ends omega).Reachable x y) :
-- imply
  typedSpinProduct (typedSpinXor sigma (typedReachabilitySpin ends omega x)) x y = -typedSpinProduct sigma x y := by
-- proof
  apply StatMech.FrontierA.typedSpinProduct_xor_reachability_of_not_reachable ends omega sigma hxy

/--
[typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (omega : P -> Bool)
  (hxy : ¬ (typedOpenGraph ends omega).Reachable x y) :
-- imply
  (∑ sigma : V -> Bool, (if TypedSignedCompatible ends ∅ omega sigma then (1 : Real) else 0) * typedSpinProduct sigma x y) = 0 := by
-- proof
  apply StatMech.FrontierA.typedCompatibleSpinProduct_sum_eq_zero_of_not_reachable ends omega hxy

/--
[typedESWeight_spinProduct_sum_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESWeight_spinProduct_sum_eq_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (rho : P -> Real)
  (omega : P -> Bool) :
-- imply
  (∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega * typedSpinProduct sigma x y) = if (typedOpenGraph ends omega).Reachable x y then typedFKWeight ends rho omega else 0 := by
-- proof
  apply StatMech.FrontierA.typedESWeight_spinProduct_sum_eq ends rho omega x y

/--
[typedESTwoPoint_eq_typedFKTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESTwoPoint_eq_typedFKTwoPoint_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (rho : P -> Real) :
-- imply
  typedESTwoPoint ends rho x y = typedFKTwoPoint ends rho x y := by
-- proof
  apply StatMech.FrontierA.typedESTwoPoint_eq_typedFKTwoPoint ends rho x y

/--
[exp_mul_typedES_spinProduct_sum_omega](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma exp_mul_typedES_spinProduct_sum_omega_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real)
  (sigma : V -> Bool) :
-- imply
  Real.exp (∑ p : P, J p) * (∑ omega : P -> Bool, typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅ sigma omega * typedSpinProduct sigma x y) = multibondIsingWeight ends J sigma * typedSpinProduct sigma x y := by
-- proof
  apply StatMech.FrontierA.exp_mul_typedES_spinProduct_sum_omega ends J sigma x y

/--
[exp_mul_typedES_twoPointNumerator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma exp_mul_typedES_twoPointNumerator_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  Real.exp (∑ p : P, J p) * (∑ omega : P -> Bool, ∑ sigma : V -> Bool, typedESWeight ends (fun p => 1 - Real.exp (-2 * J p)) ∅ sigma omega * typedSpinProduct sigma x y) = ∑ sigma : V -> Bool, multibondIsingWeight ends J sigma * typedSpinProduct sigma x y := by
-- proof
  apply StatMech.FrontierA.exp_mul_typedES_twoPointNumerator ends J x y

/--
[typedESTwoPoint_coupling_eq_multibondIsingTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedESTwoPoint_coupling_eq_multibondIsingTwoPoint_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  typedESTwoPoint ends (fun p => 1 - Real.exp (-2 * J p)) x y = multibondIsingTwoPoint ends J x y := by
-- proof
  apply StatMech.FrontierA.typedESTwoPoint_coupling_eq_multibondIsingTwoPoint ends J x y

/--
[typedFKTwoPoint_eq_multibondIsingTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean)
-/
@[path]
private lemma typedFKTwoPoint_eq_multibondIsingTwoPoint_eq
  [Fintype P]
  [DecidableEq P]
  {x y : V}
-- given
  (ends : P -> V × V)
  (J : P -> Real) :
-- imply
  typedFKTwoPoint ends (fun p => 1 - Real.exp (-2 * J p)) x y = multibondIsingTwoPoint ends J x y := by
-- proof
  apply StatMech.FrontierA.typedFKTwoPoint_eq_multibondIsingTwoPoint ends J x y


-- created on 2026-10-23
