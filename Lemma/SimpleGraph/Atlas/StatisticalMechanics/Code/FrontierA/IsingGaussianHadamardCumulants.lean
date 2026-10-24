import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants
open Filter StatMech StatMech.FrontierA


/--
[iteratedDeriv_hadamardRootLogTerm_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_hadamardRootLogTerm_odd_eq
  {r : Real}
  {m : Nat}
-- given
  (hr : 0 ≤ r)
  (hm : 1 ≤ m) :
-- imply
  iteratedDeriv (2 * m - 1) (hadamardRootLogTerm r) 0 = -2 * (-1 : Complex) ^ m * (Nat.factorial (2 * m - 1) : Complex) * (r : Complex) ^ m := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_hadamardRootLogTerm_odd r hr m hm

/--
[iteratedDeriv_hadamardRootLogTerm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_hadamardRootLogTerm_one_eq
  {r : Real}
-- given
  (hr : 0 ≤ r) :
-- imply
  iteratedDeriv 1 (hadamardRootLogTerm r) 0 = 2 * r := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_hadamardRootLogTerm_one r hr

/--
[iteratedDeriv_hadamardRootLogTerm_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_hadamardRootLogTerm_three_eq
  {r : Real}
-- given
  (hr : 0 ≤ r) :
-- imply
  iteratedDeriv 3 (hadamardRootLogTerm r) 0 = -12 * r ^ 2 := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_hadamardRootLogTerm_three r hr

/--
[hadamardRootLogTerm_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardRootLogTerm_neg_eq
  {r : Real}
  {z : Complex} :
-- imply
  hadamardRootLogTerm r (-z) = -hadamardRootLogTerm r z := by
-- proof
  apply StatMech.FrontierA.hadamardRootLogTerm_neg r z

/--
[iteratedDeriv_hadamardRootLogTerm_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_hadamardRootLogTerm_even_eq
  {r : Real}
  {order : Nat}
-- given
  (horder : Even order) :
-- imply
  iteratedDeriv order (hadamardRootLogTerm r) 0 = 0 := by
-- proof
  apply StatMech.FrontierA.iteratedDeriv_hadamardRootLogTerm_even r order horder

/--
[summableLocallyUniformlyOn_hadamardRootLogTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma summableLocallyUniformlyOn_hadamardRootLogTerm_eq
  {roots : Nat → Real}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  SummableLocallyUniformlyOn (fun n => hadamardRootLogTerm (roots n)) (hadamardRootNeighborhood roots) := by
-- proof
  apply StatMech.FrontierA.summableLocallyUniformlyOn_hadamardRootLogTerm hroots hsum

/--
[hadamardRootLogTerm_analyticOnNhd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardRootLogTerm_analyticOnNhd_eq
  {roots : Nat → Real}
  {n : Nat}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  AnalyticOnNhd Complex (hadamardRootLogTerm (roots n)) (hadamardRootNeighborhood roots) := by
-- proof
  apply StatMech.FrontierA.hadamardRootLogTerm_analyticOnNhd hroots hsum n

/--
[hasSum_iteratedDeriv_hadamardRootLogTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hasSum_iteratedDeriv_hadamardRootLogTerm_eq
  {roots : Nat → Real}
  {order : Nat}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  HasSum (fun n => iteratedDeriv order (hadamardRootLogTerm (roots n)) 0) (iteratedDeriv order (fun z => ∑' n, hadamardRootLogTerm (roots n) z) 0) := by
-- proof
  apply StatMech.FrontierA.hasSum_iteratedDeriv_hadamardRootLogTerm hroots hsum order

/--
[EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_rootSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_logDeriv_eq_rootSum_eq
  {F : Complex → Complex}
  {order : Nat}
-- given
  (hF : EvenHadamardFactorization F) :
-- imply
  iteratedDeriv order (logDeriv F) 0 = iteratedDeriv order (fun z => ∑' n, hadamardRootLogTerm (hF.roots n) z) 0 := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_rootSum hF order

/--
[EvenHadamardFactorization.iteratedDeriv_logDeriv_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_logDeriv_even_eq
  {F : Complex → Complex}
  {order : Nat}
-- given
  (hF : EvenHadamardFactorization F)
  (horder : Even order) :
-- imply
  iteratedDeriv order (logDeriv F) 0 = 0 := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.iteratedDeriv_logDeriv_even hF order horder

/--
[EvenHadamardFactorization.iteratedDeriv_logDeriv_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_logDeriv_odd_eq
  {F : Complex → Complex}
  {m : Nat}
-- given
  (hF : EvenHadamardFactorization F)
  (hm : 1 ≤ m) :
-- imply
  iteratedDeriv (2 * m - 1) (logDeriv F) 0 = -2 * (-1 : Complex) ^ m * (Nat.factorial (2 * m - 1) : Complex) * (∑' n, hF.roots n ^ m) := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.iteratedDeriv_logDeriv_odd hF m hm

/--
[normalizedIteratedDeriv_logDeriv_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma normalizedIteratedDeriv_logDeriv_recurrence_eq
  {order : Nat}
-- given
  (F : Complex -> Complex)
  (hF : AnalyticAt Complex F 0)
  (hF0 : F 0 ≠ 0) :
-- imply
  iteratedDeriv (order + 1) F 0 / F 0 = ∑ k ∈ Finset.range (order + 1), (order.choose k : Complex) * iteratedDeriv k (logDeriv F) 0 * (iteratedDeriv (order - k) F 0 / F 0) := by
-- proof
  apply StatMech.FrontierA.normalizedIteratedDeriv_logDeriv_recurrence F hF hF0 order

/--
[EvenHadamardFactorization.hadamardScalarCumulant_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardScalarCumulant_even_eq
  {F : Complex → Complex}
  {m : Nat}
-- given
  (hF : EvenHadamardFactorization F)
  (hm : 1 ≤ m) :
-- imply
  hadamardScalarCumulant F (2 * m) = -2 * (-1 : Real) ^ m * (Nat.factorial (2 * m - 1) : Real) * (∑' n, hF.roots n ^ m) := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.hadamardScalarCumulant_even hF m hm

/--
[hadamardScalarCumulant_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardScalarCumulant_zero_eq
  {F : Complex → Complex} :
-- imply
  hadamardScalarCumulant F 0 = 0 := by
-- proof
  apply StatMech.FrontierA.hadamardScalarCumulant_zero F

/--
[EvenHadamardFactorization.hadamardScalarCumulant_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardScalarCumulant_odd_eq
  {F : Complex → Complex}
  {order : Nat}
-- given
  (hF : EvenHadamardFactorization F)
  (horder : Odd order) :
-- imply
  hadamardScalarCumulant F order = 0 := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.hadamardScalarCumulant_odd hF order horder

/--
[EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma iteratedDeriv_logDeriv_eq_hadamardScalarCumulant_eq
  {F : Complex -> Complex}
  {order : Nat}
-- given
  (hF : EvenHadamardFactorization F) :
-- imply
  iteratedDeriv order (logDeriv F) 0 = (hadamardScalarCumulant F (order + 1) : Complex) := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.iteratedDeriv_logDeriv_eq_hadamardScalarCumulant hF order

/--
[EvenHadamardFactorization.hadamardScalarCumulant_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardScalarCumulant_two_eq
  {F : Complex → Complex}
-- given
  (hF : EvenHadamardFactorization F) :
-- imply
  hadamardScalarCumulant F 2 = 2 * ∑' n, hF.roots n := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.hadamardScalarCumulant_two hF

/--
[EvenHadamardFactorization.hadamardScalarCumulant_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma hadamardScalarCumulant_four_eq
  {F : Complex → Complex}
-- given
  (hF : EvenHadamardFactorization F) :
-- imply
  hadamardScalarCumulant F 4 = -12 * ∑' n, hF.roots n ^ 2 := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.hadamardScalarCumulant_four hF

/--
[newmanFourthCumulantControl_of_evenHadamardFactorizations](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma newmanFourthCumulantControl_of_evenHadamardFactorizations_eq
  {F : Nat → Complex → Complex}
-- given
  (hF : ∀ scale, EvenHadamardFactorization (F scale)) :
-- imply
  NewmanFourthCumulantControl (fun scale order => hadamardScalarCumulant (F scale) order) := by
-- proof
  apply StatMech.FrontierA.newmanFourthCumulantControl_of_evenHadamardFactorizations F hF

/--
[newmanFourthCumulantControl_of_eq_hadamardScalarCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma newmanFourthCumulantControl_of_eq_hadamardScalarCumulant_eq
-- given
  (F : Nat -> Complex -> Complex)
  (hF : forall scale, EvenHadamardFactorization (F scale))
  (cumulants : Nat -> Nat -> Real)
  (heq : forall scale order, cumulants scale order = hadamardScalarCumulant (F scale) order) :
-- imply
  NewmanFourthCumulantControl cumulants := by
-- proof
  apply StatMech.FrontierA.newmanFourthCumulantControl_of_eq_hadamardScalarCumulant F hF cumulants heq

/--
[finiteIsingWeightedRawMoment_hadamard_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedRawMoment_hadamard_recurrence_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (a : V -> Real)
  (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a) :
-- imply
  finiteIsingWeightedRawMoment G beta a (order + 1) = ∑ k ∈ Finset.range (order + 1), (order.choose k : Real) * hadamardScalarCumulant (finiteIsingWeightedFieldPartition G beta a) (k + 1) * finiteIsingWeightedRawMoment G beta a (order - k) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedRawMoment_hadamard_recurrence beta a hF order

/--
[finiteIsingWeightedCumulant_eq_hadamardScalarCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedCumulant_eq_hadamardScalarCumulant_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {order : Nat}
-- given
  (a : V -> Real)
  (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a) :
-- imply
  PhysicalIsing.finiteIsingWeightedCumulant G beta a order = hadamardScalarCumulant (finiteIsingWeightedFieldPartition G beta a) order := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedCumulant_eq_hadamardScalarCumulant beta a hF order

/--
[finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {c : Real}
  {order : Nat}
-- given
  (a : V -> Real)
  (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a) :
-- imply
  scalarCumulantsOfMoments (fun m => c ^ m * finiteIsingWeightedRawMoment G beta a m) order = hadamardScalarCumulant (fun z => finiteIsingWeightedFieldPartition G beta a ((c : Complex) * z)) order := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedScaledCumulant_eq_hadamardScalarCumulant beta a c hF order

/--
[finiteIsingWeighted_newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma finiteIsingWeighted_newmanFourthCumulantControl_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Nat → Real}
  {a : Nat → V → Real}
-- given
  (hF : ∀ scale, FiniteIsingWeightedHadamardFactorization (G := G) (beta scale) (a scale)) :
-- imply
  NewmanFourthCumulantControl (fun scale order => hadamardScalarCumulant (finiteIsingWeightedFieldPartition G (beta scale) (a scale)) order) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeighted_newmanFourthCumulantControl beta a hF

/--
[finiteIsingWeighted_physical_newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma finiteIsingWeighted_physical_newmanFourthCumulantControl_eq
  [Fintype V]
  [DecidableEq V]
-- given
  (beta : Nat -> Real)
  (a : Nat -> V -> Real)
  (hF : forall scale, FiniteIsingWeightedHadamardFactorization (G := G) (beta scale) (a scale)) :
-- imply
  NewmanFourthCumulantControl (fun scale order => PhysicalIsing.finiteIsingWeightedCumulant G (beta scale) (a scale) order) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeighted_physical_newmanFourthCumulantControl beta a hF

/--
[criticalFiniteBoxWeighted_physical_newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeighted_physical_newmanFourthCumulantControl_eq
  {d : Nat}
-- given
  (a : (n : Nat) -> sctBox d n -> Real)
  (hF : forall n, FiniteIsingWeightedHadamardFactorization (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)) :
-- imply
  NewmanFourthCumulantControl (fun n order => PhysicalIsing.finiteIsingWeightedCumulant (sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n) order) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeighted_physical_newmanFourthCumulantControl d a hF

/--
[criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl_eq
  {d : Nat}
-- given
  (hd : 2 <= d)
  (a : (n : Nat) -> sctBox d n -> Real)
  (hF : forall n, FiniteIsingWeightedHadamardFactorization (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n)) :
-- imply
  NewmanFourthCumulantControl (fun n order => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant d n hd (a n) order) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedScaled_newmanFourthCumulantControl d hd a hF

/--
[criticalFiniteBoxWeightedScaled_cumulantLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean)
-/
@[path]
private lemma criticalFiniteBoxWeightedScaled_cumulantLimits_eq
  {d : Nat}
  {variance : Real}
-- given
  (hd : 4 < d)
  (a : (n : Nat) -> sctBox d n -> Real)
  (ha0 : forall n i, 0 <= a n i)
  (ha1 : forall n i, a n i <= 1)
  (hF : forall n, FiniteIsingWeightedHadamardFactorization (G := sctBoxGraph d n) (IsingFK.betaC (magnetization d)) (a n))
  (hvariance : Tendsto (fun n => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant d n (by omega) (a n) 2) atTop (nhds variance)) :
-- imply
  forall order, Tendsto (fun n => PhysicalIsing.criticalFiniteBoxWeightedScaledCumulant d n (by omega) (a n) order) atTop (nhds (scalarGaussianCumulant variance order)) := by
-- proof
  apply StatMech.FrontierA.criticalFiniteBoxWeightedScaled_cumulantLimits d hd a ha0 ha1 hF variance hvariance


-- created on 2026-10-23
