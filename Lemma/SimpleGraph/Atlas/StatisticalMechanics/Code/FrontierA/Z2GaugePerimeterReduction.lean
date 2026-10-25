import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugePerimeterReduction.Part4
open StatMech StatMech.FrontierA


/--
[finiteEventMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma finiteEventMass_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {pi : ConfigSpace E -> Real}
  {A : Set (ConfigSpace E)}
-- given
  (hpi : 0 <= pi) :
-- imply
  0 <= finiteEventMass pi A := by
-- proof
  apply StatMech.FrontierA.finiteEventMass_nonneg hpi A

/--
[fkg_inequality_decreasing_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma fkg_inequality_decreasing_events_eq
  [Fintype E]
  [DecidableEq E]
  {pi : ConfigSpace E -> Real}
  {A B : Set (ConfigSpace E)}
-- given
  (hpi : 0 <= pi)
  (hnorm : ∑ omega, pi omega = 1)
  (hlattice : FKGLatticeCondition pi)
  (hA : IsDecreasing A)
  (hB : IsDecreasing B) :
-- imply
  finiteEventMass pi A * finiteEventMass pi B <= finiteEventMass pi (A ∩ B) := by
-- proof
  apply StatMech.FrontierA.fkg_inequality_decreasing_events hpi hnorm hlattice hA hB

/--
[finiteEventInter_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma finiteEventInter_decreasing_eq
  {s : Finset I}
  {A : I -> Set (ConfigSpace E)}
-- given
  (hA : forall i, i ∈ s -> IsDecreasing (A i)) :
-- imply
  IsDecreasing (finiteEventInter s A) := by
-- proof
  apply StatMech.FrontierA.finiteEventInter_decreasing hA

/--
[fkg_inequality_finite_decreasing_events](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma fkg_inequality_finite_decreasing_events_eq
  [Fintype E]
  [DecidableEq E]
  {pi : ConfigSpace E -> Real}
  {s : Finset I}
-- given
  (hpi : 0 <= pi)
  (hnorm : ∑ omega, pi omega = 1)
  (hlattice : FKGLatticeCondition pi)
  (A : I -> Set (ConfigSpace E))
  (hA : forall i, i ∈ s -> IsDecreasing (A i)) :
-- imply
  (∏ i ∈ s, finiteEventMass pi (A i)) <= finiteEventMass pi (finiteEventInter s A) := by
-- proof
  apply StatMech.FrontierA.fkg_inequality_finite_decreasing_events hpi hnorm hlattice s A hA

/--
[fkDisconnEvent_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma fkDisconnEvent_decreasing_eq
  {G : SimpleGraph V}
  {x y : V} :
-- imply
  IsDecreasing (fkDisconnEvent G x y) := by
-- proof
  apply StatMech.FrontierA.fkDisconnEvent_decreasing G x y

/--
[finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : Real}
  {x y : V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  finiteEventMass (FK.fkProb G p q) (fkDisconnEvent G x y) = 1 - FK.twoPointFun G p q x y := by
-- proof
  apply StatMech.FrontierA.finiteEventMass_fkDisconnEvent_eq_one_sub_twoPointFun G hp hp1 hq x y

/--
[fk_finite_pair_nonconnection_product_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma fk_finite_pair_nonconnection_product_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : Real}
  {s : Finset I}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (x y : I -> V) :
-- imply
  (∏ i ∈ s, (1 - FK.twoPointFun G p q (x i) (y i))) <= finiteEventMass (FK.fkProb G p q) (finiteEventInter s (fun i => fkDisconnEvent G (x i) (y i))) := by
-- proof
  apply StatMech.FrontierA.fk_finite_pair_nonconnection_product_bound G hp hp1 hq s x y

/--
[gaugePerimeterPenalty_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma gaugePerimeterPenalty_pos_eq
  {R : Real}
-- given
  (hR0 : 0 < R)
  (hR1 : R < 1) :
-- imply
  0 < gaugePerimeterPenalty R := by
-- proof
  apply StatMech.FrontierA.gaugePerimeterPenalty_pos hR0 hR1

/--
[exp_neg_gaugePerimeterPenalty_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma exp_neg_gaugePerimeterPenalty_mul_eq
  {R : Real}
-- given
  (hR0 : 0 < R)
  (hR1 : R < 1) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R) * R) = 1 - R := by
-- proof
  apply StatMech.FrontierA.exp_neg_gaugePerimeterPenalty_mul R hR0 hR1

/--
[exp_neg_gaugePerimeterPenalty_mul_le_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma exp_neg_gaugePerimeterPenalty_mul_le_one_sub_eq
  {R r : Real}
-- given
  (hR0 : 0 < R)
  (hR1 : R < 1)
  (hr0 : 0 <= r)
  (hrR : r <= R) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R) * r) <= 1 - r := by
-- proof
  apply StatMech.FrontierA.exp_neg_gaugePerimeterPenalty_mul_le_one_sub hR0 hR1 hr0 hrR

/--
[exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub_eq
  {R : Real}
  {s : Finset I}
-- given
  (hR0 : 0 < R)
  (hR1 : R < 1)
  (r : I -> Real)
  (hr0 : forall i : I, i ∈ s -> 0 <= r i)
  (hrR : forall i : I, i ∈ s -> r i <= R) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R) * (∑ i ∈ s, r i)) <= ∏ i ∈ s, (1 - r i) := by
-- proof
  apply StatMech.FrontierA.exp_neg_gaugePerimeterPenalty_mul_sum_le_prod_one_sub hR0 hR1 s r hr0 hrR

/--
[gauge_perimeterLaw_of_product_and_sum_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma gauge_perimeterLaw_of_product_and_sum_bounds_eq
  {R C perimeter wilson : Real}
  {s : Finset I}
-- given
  (hR0 : 0 < R)
  (hR1 : R < 1)
  (r : I -> Real)
  (hr0 : forall i : I, i ∈ s -> 0 <= r i)
  (hrR : forall i : I, i ∈ s -> r i <= R)
  (hproduct : (∏ i ∈ s, (1 - r i)) <= wilson)
  (hsum : (∑ i ∈ s, r i) <= C * perimeter) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= wilson := by
-- proof
  apply StatMech.FrontierA.gauge_perimeterLaw_of_product_and_sum_bounds hR0 hR1 s r hr0 hrR hproduct hsum

/--
[fk_perimeterLaw_of_cylinder_bridge_and_sum_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugePerimeterReduction.lean)
-/
@[path]
private lemma fk_perimeterLaw_of_cylinder_bridge_and_sum_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q R C perimeter wilson : Real}
  {s : Finset I}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hR0 : 0 < R)
  (hR1 : R < 1)
  (x y : I -> V)
  (hR : forall i, i ∈ s -> FK.twoPointFun G p q (x i) (y i) <= R)
  (hcylinder : finiteEventMass (FK.fkProb G p q) (finiteEventInter s (fun i => fkDisconnEvent G (x i) (y i))) <= wilson)
  (hsum : (∑ i ∈ s, FK.twoPointFun G p q (x i) (y i)) <= C * perimeter) :
-- imply
  Real.exp (-(gaugePerimeterPenalty R * C) * perimeter) <= wilson := by
-- proof
  apply StatMech.FrontierA.fk_perimeterLaw_of_cylinder_bridge_and_sum_bound G hp hp1 hq hR0 hR1 s x y hR hcylinder hsum


-- created on 2026-10-23
