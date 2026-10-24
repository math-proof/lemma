import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRegularity
open StatMech StatMech.Universality


/--
[isingCellCRAt_leapfrog_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingCellCRAt_leapfrog_harmonic_eq
  {F : Nat → Nat → Complex}
  {i j : Nat}
-- given
  (hSW : IsingCellCRAt F i j)
  (hSE : IsingCellCRAt F (i + 1) j)
  (hNW : IsingCellCRAt F i (j + 1))
  (hNE : IsingCellCRAt F (i + 1) (j + 1)) :
-- imply
  F i j + F i (j + 2) + F (i + 2) j + F (i + 2) (j + 2) = 4 * F (i + 1) (j + 1) := by
-- proof
  apply StatMech.Universality.isingCellCRAt_leapfrog_harmonic F i j hSW hSE hNW hNE

/--
[fkIsingSquareRadialPatchFullObservableExtension_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservableExtension_apply_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchFullObservableExtension n m hn hm i j = fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservableExtension_apply n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatchFullObservable_cellCR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservable_cellCR_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 2 < m)
  (hj : j + 2 < m) :
-- imply
  IsingCellCRAt (fkIsingSquareRadialPatchFullObservableExtension n m hn hm) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservable_cellCR n m i j hn hm hi hj

/--
[fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 3 < m)
  (hj : j + 3 < m) :
-- imply
  fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩ + fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j + 2, by omega⟩ + fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i + 2, by omega⟩ ⟨j, by omega⟩ + fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i + 2, by omega⟩ ⟨j + 2, by omega⟩ = 4 * fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i + 1, by omega⟩ ⟨j + 1, by omega⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservable_leapfrog_harmonic n m i j hn hm hi hj

/--
[isingCentralBinom_sq_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingCentralBinom_sq_mul_le_eq
  {n : Nat} :
-- imply
  ((Nat.centralBinom n : Real) ^ 2) * (2 * n + 1) ≤ (16 : Real) ^ n := by
-- proof
  apply StatMech.Universality.isingCentralBinom_sq_mul_le n

/--
[isingBinomialWeight_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingBinomialWeight_sq_sum_eq
  {n : Nat} :
-- imply
  ∑ k ∈ range (n + 1), isingBinomialWeight n k ^ 2 = (Nat.centralBinom n : Real) / 4 ^ n := by
-- proof
  apply StatMech.Universality.isingBinomialWeight_sq_sum n

/--
[isingBinomialWeight_diff_sq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingBinomialWeight_diff_sq_sum_eq
  {n : Nat} :
-- imply
  ∑ k ∈ range (n + 2), (isingBinomialWeight n k - isingBinomialWeightPrev n k) ^ 2 = 2 * (Nat.centralBinom n : Real) / ((n + 1) * 4 ^ n) := by
-- proof
  apply StatMech.Universality.isingBinomialWeight_diff_sq_sum n

/--
[isingBinomialKernel_gradient_sq_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingBinomialKernel_gradient_sq_sum_le_eq
  {n : Nat} :
-- imply
  (∑ a ∈ range (n + 2), ∑ b ∈ range (n + 1), ((isingBinomialWeight n a - isingBinomialWeightPrev n a) * isingBinomialWeight n b) ^ 2) ≤ 2 / ((n + 1 : Real) ^ 2) := by
-- proof
  apply StatMech.Universality.isingBinomialKernel_gradient_sq_sum_le n

/--
[isingComplex_normSq_sum_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingComplex_normSq_sum_mul_le_eq
  {ι : Type}
  {s : Finset ι}
  {c : ι → Real}
  {z : ι → Complex} :
-- imply
  Complex.normSq (∑ x ∈ s, (c x : Complex) * z x) ≤ (∑ x ∈ s, c x ^ 2) * (∑ x ∈ s, Complex.normSq (z x)) := by
-- proof
  apply StatMech.Universality.isingComplex_normSq_sum_mul_le s c z

/--
[isingBinomialMean_normSq_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRegularity.lean)
-/
@[path]
private lemma isingBinomialMean_normSq_sub_le_eq
  {F : Nat → Nat → Complex}
  {t x y : Nat}
  {E : Real}
  {left right : Complex}
-- given
  (hleft : left = ∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1), ((isingBinomialWeight t a * isingBinomialWeight t b : Real) : Complex) * F (x + 2 * a) (y + 2 * b))
  (hright : right = ∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1), ((isingBinomialWeightPrev t a * isingBinomialWeight t b : Real) : Complex) * F (x + 2 * a) (y + 2 * b))
  (hL2 : (∑ a ∈ range (t + 2), ∑ b ∈ range (t + 1), Complex.normSq (F (x + 2 * a) (y + 2 * b))) ≤ E) :
-- imply
  Complex.normSq (left - right) ≤ 2 * E / (t + 1 : Real) ^ 2 := by
-- proof
  apply StatMech.Universality.isingBinomialMean_normSq_sub_le F t x y E left right hleft hright hL2


-- created on 2026-10-23
