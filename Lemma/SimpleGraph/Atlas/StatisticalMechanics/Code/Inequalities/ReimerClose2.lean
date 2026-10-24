import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Inequalities.ReimerClose2
open MeasureTheory Finset StatMech


/--
[wprob_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma wprob_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {S : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b) :
-- imply
  0 ≤ wprob φ S := by
-- proof
  apply StatMech.wprob_nonneg hφ0 S

/--
[wprob_disjointOccurrence_le_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma wprob_disjointOccurrence_le_inter_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ (A ∩ B) := by
-- proof
  apply StatMech.wprob_disjointOccurrence_le_inter hφ0 A B

/--
[reimer_wprob_of_negCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimer_wprob_of_negCorr_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (h : NegativelyCorrelated φ A B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_of_negCorr hφ0 h

/--
[reimer_wprob_of_inter_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimer_wprob_of_inter_empty_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (h : A ∩ B = ∅) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_of_inter_empty hφ0 h

/--
[reimer_inequality_of_inter_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimer_inequality_of_inter_empty_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (h : A ∩ B = ∅) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimer_inequality_of_inter_empty hp h

/--
[evXor_inter_evXnor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma evXor_inter_evXnor_eq :
-- imply
  evXor ∩ evXnor = ∅ := by
-- proof
  apply StatMech.evXor_inter_evXnor

/--
[not_isIncreasing_evXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma not_isIncreasing_evXor_eq :
-- imply
  ¬ IsIncreasing evXor := by
-- proof
  apply StatMech.not_isIncreasing_evXor

/--
[not_isDecreasing_evXor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma not_isDecreasing_evXor_eq :
-- imply
  ¬ IsDecreasing evXor := by
-- proof
  apply StatMech.not_isDecreasing_evXor

/--
[reimer_xor_xnor_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimer_xor_xnor_inequality_eq
  {p : ℝ≥0}
-- given
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := Fin 2) p hp).real (disjointOccurrence evXor evXnor) ≤ (bernoulliProductMeasure (E := Fin 2) p hp).real evXor * (bernoulliProductMeasure (E := Fin 2) p hp).real evXnor := by
-- proof
  apply StatMech.reimer_xor_xnor_inequality hp

/--
[reimerCore_succ_of_sliceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimerCore_succ_of_sliceStep_eq
  {n : ℕ}
  {φ : Fin (n + 1) → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin (n + 1)))}
-- given
  (hcore : ∀ (φ : Fin n → Bool → ℝ), (∀ i b, 0 ≤ φ i b) → (∀ i, φ i false + φ i true = 1) → ∀ (A B : Set (ConfigSpace (Fin n))), wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B)
  (hstep : ReimerSliceStep n)
  (hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimerCore_succ_of_sliceStep n hcore hstep φ hφ0 hφ1 A B

/--
[reimer_wprobCore_of_sliceStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimer_wprobCore_of_sliceStep_eq
-- given
  (hstep : ∀ n, ReimerSliceStep n) :
-- imply
  ReimerWprobCore := by
-- proof
  apply StatMech.reimer_wprobCore_of_sliceStep hstep

/--
[reimerSliceStep_holds_on_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimerSliceStep_holds_on_increasing_eq
  {n : ℕ}
  {ψ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin (n + 1)))}
-- given
  (hψ0 : ∀ i b, 0 ≤ ψ i b)
  (hψ1 : ∀ i, ψ i false + ψ i true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  wprob ψ (disjointOccurrence (slice A false) (slice B false)) ≤ wprob ψ (disjointOccurrence (slice A false) (slice B true) ∩ disjointOccurrence (slice A true) (slice B false)) ∧ wprob ψ (disjointOccurrence (slice A false) (slice B true) ∪ disjointOccurrence (slice A true) (slice B false)) ≤ wprob ψ (slice A true) * wprob ψ (slice B true) := by
-- proof
  apply StatMech.reimerSliceStep_holds_on_increasing n ψ hψ0 hψ1 A B hA hB

/--
[reimerSliceStep_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerClose2.lean)
-/
@[path]
private lemma reimerSliceStep_satisfiable_eq
  {n : ℕ}
  {ψ : Fin n → Bool → ℝ}
-- given
  (hψ0 : ∀ i b, 0 ≤ ψ i b)
  (hψ1 : ∀ i, ψ i false + ψ i true = 1) :
-- imply
  wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false) (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false)) ≤ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false) (slice Set.univ true) ∩ disjointOccurrence (slice Set.univ true) (slice Set.univ false)) ∧ wprob ψ (disjointOccurrence (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) false) (slice Set.univ true) ∪ disjointOccurrence (slice Set.univ true) (slice Set.univ false)) ≤ wprob ψ (slice (Set.univ : Set (ConfigSpace (Fin (n + 1)))) true) * wprob ψ (slice Set.univ true) := by
-- proof
  apply StatMech.reimerSliceStep_satisfiable n ψ hψ0 hψ1


-- created on 2026-10-23
