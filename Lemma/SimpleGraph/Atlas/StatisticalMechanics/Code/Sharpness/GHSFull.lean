import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.GHSFull.Part3
open Finset SimpleGraph Set StatMech StatMech.Sharpness


/--
[hasDerivAt_isingWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma hasDerivAt_isingWeight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingWeight G β h s) (isingWeight G β h s * (β * ∑ x, spin s x)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_isingWeight G β h s

/--
[hasDerivAt_num](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma hasDerivAt_num_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => ∑ s : ConfigSpace V, f s * isingWeight G β h s) (∑ s : ConfigSpace V, f s * (isingWeight G β h s * (β * ∑ x, spin s x))) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_num G β h f

/--
[hasDerivAt_isingZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma hasDerivAt_isingZ_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingZ G β h) (∑ s : ConfigSpace V, isingWeight G β h s * (β * ∑ x, spin s x)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_isingZ G β h

/--
[expectation_eq_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_eq_div_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h f = (∑ s : ConfigSpace V, f s * isingWeight G β h s) / isingZ G β h := by
-- proof
  apply StatMech.Sharpness.expectation_eq_div G β h f

/--
[hasDerivAt_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma hasDerivAt_expectation_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingExpectation G β h f) (β * (isingExpectation G β h (fun s => f s * totalSpin s) - isingExpectation G β h f * isingExpectation G β h totalSpin)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_expectation G β h f

/--
[expectation_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : Finset ι}
  {f : ι → ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun cfg => ∑ i ∈ s, f i cfg) = ∑ i ∈ s, isingExpectation G β h (f i) := by
-- proof
  apply StatMech.Sharpness.expectation_sum G β h s f

/--
[expectation_totalSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_totalSpin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h totalSpin = ∑ x, isingExpectation G β h (fun s => spin s x) := by
-- proof
  apply StatMech.Sharpness.expectation_totalSpin G β h

/--
[expectation_mul_totalSpin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_mul_totalSpin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {f : ConfigSpace V → ℝ}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => f s * totalSpin s) = ∑ x, isingExpectation G β h (fun s => f s * spin s x) := by
-- proof
  apply StatMech.Sharpness.expectation_mul_totalSpin G β h f

/--
[spinProd_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma spinProd_singleton_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V} :
-- imply
  spinProd ({x} : Finset V) = (fun s => spin s x) := by
-- proof
  apply StatMech.Sharpness.spinProd_singleton G x

/--
[spinProd_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma spinProd_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  spinProd ({x, y} : Finset V) = (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Sharpness.spinProd_pair G x y hxy

/--
[symmDiff_singleton_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma symmDiff_singleton_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (hxy : x ≠ y) :
-- imply
  symmDiff ({x} : Finset V) {y} = {x, y} := by
-- proof
  apply StatMech.Sharpness.symmDiff_singleton_pair G x y hxy

/--
[expectation_spin_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_spin_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun s => spin s x) ≤ 1 := by
-- proof
  apply StatMech.Sharpness.expectation_spin_le_one G β h x

/--
[expectation_spin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_spin_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation G β h (fun s => spin s x) := by
-- proof
  apply StatMech.Sharpness.expectation_spin_nonneg G β h hβ hh x

/--
[expectation_spin_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma expectation_spin_bounds_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ isingExpectation G β h (fun s => spin s x) ∧ isingExpectation G β h (fun s => spin s x) ≤ 1 := by
-- proof
  apply StatMech.Sharpness.expectation_spin_bounds G β h hβ hh x

/--
[cov_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma cov_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {x y : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h)
  (hxy : x ≠ y) :
-- imply
  isingExpectation G β h (fun s => spin s x) * isingExpectation G β h (fun s => spin s y) ≤ isingExpectation G β h (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Sharpness.cov_nonneg G β h hβ hh x y hxy

/--
[hasDerivAt_magnetization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma hasDerivAt_magnetization_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o)) (β * (isingExpectation G β h (fun s => spin s o * totalSpin s) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin)) h := by
-- proof
  apply StatMech.Sharpness.hasDerivAt_magnetization G β h o

/--
[deriv_magnetization_eq_sum_cov](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma deriv_magnetization_eq_sum_cov_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) h = β * ∑ x, (isingExpectation G β h (fun s => spin s o * spin s x) - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)) := by
-- proof
  apply StatMech.Sharpness.deriv_magnetization_eq_sum_cov G β h o

/--
[deriv_magnetization_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma deriv_magnetization_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hβ : 0 ≤ β)
  (hh : 0 ≤ h) :
-- imply
  0 ≤ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h := by
-- proof
  apply StatMech.Sharpness.deriv_magnetization_nonneg G β h hβ hh o

/--
[spin_flipCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma spin_flipCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {x : V} :
-- imply
  spin (flipCfg s) x = - spin s x := by
-- proof
  apply StatMech.Sharpness.spin_flipCfg G s x

/--
[bond_flipCfg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma bond_flipCfg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {s : ConfigSpace V}
  {e : Sym2 V} :
-- imply
  bond (flipCfg s) e = bond s e := by
-- proof
  apply StatMech.Sharpness.bond_flipCfg G s e

/--
[magnetization_zero_field](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma magnetization_zero_field_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  isingExpectation G β 0 (fun s => spin s o) = 0 := by
-- proof
  apply StatMech.Sharpness.magnetization_zero_field G β o

/--
[ghs_susceptibility_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSFull.lean)
-/
@[path]
private lemma ghs_susceptibility_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hh : 0 < h)
  (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ isingExpectation G β h (fun s => spin s o) / h ∧ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ 1 / h := by
-- proof
  apply StatMech.Sharpness.ghs_susceptibility_bound G β h hh o hconc


-- created on 2026-10-23
