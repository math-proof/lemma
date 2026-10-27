import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicLineGambler.Part3
open StatMech StatMech.Universality


/--
[isingLineStoppedKernel_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedKernel_nonneg_eq
  {n t : Nat}
  {p q : IsingLineBox n} :
-- imply
  0 ≤ isingLineStoppedKernel n t p q := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_nonneg n t p q

/--
[isingLineStoppedKernel_sum_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedKernel_sum_eq_one_eq
  {n t : Nat}
  {p : IsingLineBox n} :
-- imply
  ∑ q, isingLineStoppedKernel n t p q = 1 := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_sum_eq_one n t p

/--
[isingLineStoppedMean_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedMean_succ_eq
  {n t : Nat}
  {f : IsingLineBox n → Real}
  {p : IsingLineBox n} :
-- imply
  isingLineStoppedMean n (t + 1) f p = if hp : isingLineBoxBoundary n p then isingLineStoppedMean n t f p else (isingLineStoppedMean n t f (isingLineWest n p) + isingLineStoppedMean n t f (isingLineEast n p hp)) / 2 := by
-- proof
  apply StatMech.Universality.isingLineStoppedMean_succ n t f p

/--
[IsingLineHarmonic.stoppedMean_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma stoppedMean_eq_eq
  {n : Nat}
  {f : IsingLineBox n → Real}
  {t : Nat}
  {p : IsingLineBox n}
-- given
  (hf : IsingLineHarmonic n f) :
-- imply
  isingLineStoppedMean n t f p = f p := by
-- proof
  apply StatMech.Universality.IsingLineHarmonic.stoppedMean_eq hf t p

/--
[isingLineDistanceToRight_harmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineDistanceToRight_harmonic_eq
  {n : Nat} :
-- imply
  IsingLineHarmonic n (fun p => (n - p.1 : Nat)) := by
-- proof
  apply StatMech.Universality.isingLineDistanceToRight_harmonic n

/--
[isingLineStoppedMean_distanceToRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedMean_distanceToRight_eq
  {n t : Nat}
  {p : IsingLineBox n} :
-- imply
  isingLineStoppedMean n t (fun q => (n - q.1 : Nat)) p = (n - p.1 : Nat) := by
-- proof
  apply StatMech.Universality.isingLineStoppedMean_distanceToRight n t p

/--
[isingLineStoppedKernel_left_mul_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedKernel_left_mul_le_eq
  {n t : Nat}
  {p : IsingLineBox n} :
-- imply
  (n : Real) * isingLineStoppedKernel n t p ⟨0, by omega⟩ ≤ (n - p.1 : Nat) := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_left_mul_le n t p

/--
[isingLineStoppedKernel_left_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedKernel_left_le_eq
  {n t : Nat}
  {p : IsingLineBox n}
-- given
  (hn : 0 < n) :
-- imply
  isingLineStoppedKernel n t p ⟨0, by omega⟩ ≤ ((n - p.1 : Nat) : Real) / n := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_left_le n t p hn

/--
[isingLineStoppedKernel_left_of_rightNeighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedKernel_left_of_rightNeighbor_eq
  {n t : Nat}
-- given
  (hn : 0 < n) :
-- imply
  isingLineStoppedKernel n t ⟨n - 1, by omega⟩ ⟨0, by omega⟩ ≤ 1 / (n : Real) := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_left_of_rightNeighbor n t hn

/--
[isingLineStoppedKernel_eq_natCard_choicePath_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicLineGambler.lean)
-/
@[path]
private lemma isingLineStoppedKernel_eq_natCard_choicePath_div_eq
  {n t : Nat}
  {p q : IsingLineBox n} :
-- imply
  isingLineStoppedKernel n t p q = Nat.card (IsingLineChoicePathFamily n t p q) / (2 : Real) ^ t := by
-- proof
  apply StatMech.Universality.isingLineStoppedKernel_eq_natCard_choicePath_div n t p q


-- created on 2026-10-23
