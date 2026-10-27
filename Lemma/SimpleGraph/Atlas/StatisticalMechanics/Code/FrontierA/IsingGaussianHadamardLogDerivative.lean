import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
open StatMech StatMech.FrontierA


/--
[multipliableLocallyUniformlyOn_hadamardRootFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma multipliableLocallyUniformlyOn_hadamardRootFactor_eq
  {roots : Nat → Real}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  MultipliableLocallyUniformlyOn (hadamardRootFactor roots) Set.univ := by
-- proof
  apply StatMech.FrontierA.multipliableLocallyUniformlyOn_hadamardRootFactor hroots hsum

/--
[isOpen_hadamardRootNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma isOpen_hadamardRootNeighborhood_eq
  {roots : Nat → Real} :
-- imply
  IsOpen (hadamardRootNeighborhood roots) := by
-- proof
  apply StatMech.FrontierA.isOpen_hadamardRootNeighborhood roots

/--
[zero_mem_hadamardRootNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma zero_mem_hadamardRootNeighborhood_eq
  {roots : Nat → Real}
-- given
  (hroots : ∀ n, 0 ≤ roots n) :
-- imply
  (0 : Complex) ∈ hadamardRootNeighborhood roots := by
-- proof
  apply StatMech.FrontierA.zero_mem_hadamardRootNeighborhood hroots

/--
[hadamardRootFactor_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma hadamardRootFactor_ne_zero_eq
  {roots : Nat → Real}
  {z : Complex}
  {n : Nat}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots)
  (hz : z ∈ hadamardRootNeighborhood roots) :
-- imply
  hadamardRootFactor roots n z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.hadamardRootFactor_ne_zero hroots hsum hz n

/--
[summable_norm_hadamardRootFactor_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma summable_norm_hadamardRootFactor_sub_one_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots) :
-- imply
  Summable fun n => ‖(roots n : Complex) * z ^ 2‖ := by
-- proof
  apply StatMech.FrontierA.summable_norm_hadamardRootFactor_sub_one hroots hsum z

/--
[logDeriv_hadamardRootFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma logDeriv_hadamardRootFactor_eq
  {roots : Nat → Real}
  {n : Nat}
  {z : Complex} :
-- imply
  logDeriv (hadamardRootFactor roots n) z = 2 * (roots n : Complex) * z / (1 + (roots n : Complex) * z ^ 2) := by
-- proof
  apply StatMech.FrontierA.logDeriv_hadamardRootFactor roots n z

/--
[summable_logDeriv_hadamardRootFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma summable_logDeriv_hadamardRootFactor_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots)
  (hz : z ∈ hadamardRootNeighborhood roots) :
-- imply
  Summable fun n => logDeriv (hadamardRootFactor roots n) z := by
-- proof
  apply StatMech.FrontierA.summable_logDeriv_hadamardRootFactor hroots hsum hz

/--
[hadamardRootProduct_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma hadamardRootProduct_ne_zero_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots)
  (hz : z ∈ hadamardRootNeighborhood roots) :
-- imply
  hadamardRootProduct roots z ≠ 0 := by
-- proof
  apply StatMech.FrontierA.hadamardRootProduct_ne_zero hroots hsum hz

/--
[logDeriv_hadamardRootProduct_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma logDeriv_hadamardRootProduct_eq_tsum_eq
  {roots : Nat → Real}
  {z : Complex}
-- given
  (hroots : ∀ n, 0 ≤ roots n)
  (hsum : Summable roots)
  (hz : z ∈ hadamardRootNeighborhood roots) :
-- imply
  logDeriv (hadamardRootProduct roots) z = ∑' n, 2 * (roots n : Complex) * z / (1 + (roots n : Complex) * z ^ 2) := by
-- proof
  apply StatMech.FrontierA.logDeriv_hadamardRootProduct_eq_tsum hroots hsum hz

/--
[EvenHadamardFactorization.logDeriv_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma logDeriv_eq_tsum_eq
  {F : Complex → Complex}
  {z : Complex}
-- given
  (hF : EvenHadamardFactorization F)
  (hz : z ∈ hadamardRootNeighborhood hF.roots) :
-- imply
  logDeriv F z = ∑' n, 2 * (hF.roots n : Complex) * z / (1 + (hF.roots n : Complex) * z ^ 2) := by
-- proof
  apply StatMech.FrontierA.EvenHadamardFactorization.logDeriv_eq_tsum hF hz

/--
[finiteIsingWeightedFieldPartition_logDeriv_eq_tsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean)
-/
@[path]
private lemma finiteIsingWeightedFieldPartition_logDeriv_eq_tsum_eq
  [Fintype V]
  [DecidableEq V]
  {beta : Real}
  {a : V → Real}
  {z : Complex}
-- given
  (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
  (hz : z ∈ hadamardRootNeighborhood hF.roots) :
-- imply
  logDeriv (finiteIsingWeightedFieldPartition G beta a) z = ∑' n, 2 * (hF.roots n : Complex) * z / (1 + (hF.roots n : Complex) * z ^ 2) := by
-- proof
  apply StatMech.FrontierA.finiteIsingWeightedFieldPartition_logDeriv_eq_tsum beta a hF hz


-- created on 2026-10-23
