import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianGrowingScalingLimit
open Filter Finset MeasureTheory Set Topology StatMech StatMech.FrontierA


/--
[compactTorusWeight_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean)
-/
@[path]
private lemma compactTorusWeight_scale_eq
  {d : Nat}
  {A : Finset (Site d)}
  {a : Site d → Real}
  {c : Real}
  {n : Nat} :
-- imply
  compactTorusWeight A (fun x ↦ c * a x) n = fun z ↦ c * compactTorusWeight A a n z := by
-- proof
  apply StatMech.FrontierA.compactTorusWeight_scale A a c n

/--
[finiteIsingWeightedRawMoment_scale_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_scale_weight_eq
  {d : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {a : V → Real}
  {c : Real}
  {order : Nat} :
-- imply
  finiteIsingWeightedRawMoment G beta (fun x ↦ c * a x) order = c ^ order * finiteIsingWeightedRawMoment G beta a order := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMoment_scale_weight G beta a c order

/--
[integral_pow_criticalTorusGrowingCanonicalFieldLaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean)
-/
@[path]
private lemma integral_pow_criticalTorusGrowingCanonicalFieldLaw_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
  {boxScale torusScale : Nat → Nat}
  {n order : Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  (∫ x, x ^ order ∂(criticalTorusGrowingCanonicalFieldLaw hd A a boxScale torusScale n : Measure Real)) = finiteIsingWeightedRawMoment (isingTorusGraph d (torusScale n)) (IsingFK.betaC (magnetization d)) (compactTorusWeight (A n) (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d (boxScale n) hd * a n x) (torusScale n)) order := by
-- proof
  apply StatMech.FrontierA.integral_pow_criticalTorusGrowingCanonicalFieldLaw hd A a boxScale torusScale n order

/--
[criticalTorusGrowingCanonical_hasScalarMomentCumulantRecurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean)
-/
@[path]
private lemma criticalTorusGrowingCanonical_hasScalarMomentCumulantRecurrence_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
  {boxScale torusScale : Nat → Nat}
-- given
  (hd : 2 ≤ d) :
-- imply
  HasScalarMomentCumulantRecurrence (fun n order ↦ ∫ x, x ^ order ∂(criticalTorusGrowingCanonicalFieldLaw hd A a boxScale torusScale n : Measure Real)) (fun n order ↦ criticalTorusCompactWeightedCumulant (A n) (fun x ↦ PhysicalIsing.criticalFiniteBoxWeightedFourthScale d (boxScale n) hd * a n x) (torusScale n) order) := by
-- proof
  apply StatMech.FrontierA.criticalTorusGrowingCanonical_hasScalarMomentCumulantRecurrence hd A a boxScale torusScale

/--
[exists_criticalTorusGrowingCanonical_weakLimit_wick](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean)
-/
@[path]
private lemma exists_criticalTorusGrowingCanonical_weakLimit_wick_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 4 < d)
  (ha0 : ∀ n x, 0 ≤ a n x)
  (ha1 : ∀ n x, a n x ≤ 1) :
-- imply
  ∃ boxScale torusScale : Nat → Nat, Tendsto boxScale atTop atTop ∧ Tendsto torusScale atTop atTop ∧ (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧ ∀ (mu : ProbabilityMeasure Real) (s C : Real), 0 < s → Tendsto (criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale) atTop (nhds mu) → (∀ n, Integrable (fun x : Real ↦ Real.exp (s * |x|)) (criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale n : Measure Real)) → (∀ n, (∫ x, Real.exp (s * |x|) ∂(criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale n : Measure Real)) ≤ C) → ScalarWickMoments (∫ x, x ^ 2 ∂(mu : Measure Real)) (fun order ↦ ∫ x, x ^ order ∂(mu : Measure Real)) := by
-- proof
  apply StatMech.FrontierA.exists_criticalTorusGrowingCanonical_weakLimit_wick hd A a ha0 ha1

/--
[exists_criticalTorusGrowingCanonical_weakLimit_eq_wickReference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean)
-/
@[path]
private lemma exists_criticalTorusGrowingCanonical_weakLimit_eq_wickReference_eq
  {d : Nat}
  {A : Nat → Finset (Site d)}
  {a : Nat → Site d → Real}
-- given
  (hd : 4 < d)
  (ha0 : ∀ n x, 0 ≤ a n x)
  (ha1 : ∀ n x, a n x ≤ 1) :
-- imply
  ∃ boxScale torusScale : Nat → Nat, Tendsto boxScale atTop atTop ∧ Tendsto torusScale atTop atTop ∧ (∀ n, (↑(A n) : Set (Site d)) ⊆ box d (boxScale n)) ∧ ∀ (mu nu : ProbabilityMeasure Real) (s C : Real), 0 < s → Tendsto (criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale) atTop (nhds mu) → (∀ n, Integrable (fun x : Real ↦ Real.exp (s * |x|)) (criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale n : Measure Real)) → (∀ n, (∫ x, Real.exp (s * |x|) ∂(criticalTorusGrowingCanonicalFieldLaw (by omega) A a boxScale torusScale n : Measure Real)) ≤ C) → (0 : Real) ∈ interior (integrableExpSet id (nu : Measure Real)) → ScalarWickMoments (∫ x, x ^ 2 ∂(mu : Measure Real)) (fun order ↦ ∫ x, x ^ order ∂(nu : Measure Real)) → (mu : Measure Real) = (nu : Measure Real) := by
-- proof
  apply StatMech.FrontierA.exists_criticalTorusGrowingCanonical_weakLimit_eq_wickReference hd A a ha0 ha1


-- created on 2026-10-23
