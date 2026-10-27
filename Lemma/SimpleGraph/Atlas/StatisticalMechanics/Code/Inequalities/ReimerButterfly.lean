import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
open MeasureTheory Finset StatMech


/--
[pweight_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma pweight_total_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
-- given
  (hφ1 : ∀ x, φ x false + φ x true = 1) :
-- imply
  ∑ ω, pweight φ ω = 1 := by
-- proof
  apply StatMech.pweight_total φ hφ1

/--
[wprob_eq_mass_mul_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma wprob_eq_mass_mul_indicator_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {S : Set (ConfigSpace E)} :
-- imply
  wprob φ S = ∑ ω, pweight φ ω * S.indicator (fun _ => (1 : ℝ)) ω := by
-- proof
  apply StatMech.wprob_eq_mass_mul_indicator φ S

/--
[wprob_add_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma wprob_add_compl_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {B : Set (ConfigSpace E)}
-- given
  (hφ1 : ∀ x, φ x false + φ x true = 1) :
-- imply
  wprob φ B + wprob φ Bᶜ = 1 := by
-- proof
  apply StatMech.wprob_add_compl φ hφ1 B

/--
[wprob_inter_add_inter_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma wprob_inter_add_inter_compl_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)} :
-- imply
  wprob φ (A ∩ B) + wprob φ (A ∩ Bᶜ) = wprob φ A := by
-- proof
  apply StatMech.wprob_inter_add_inter_compl φ A B

/--
[pweight_fkgLatticeCondition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma pweight_fkgLatticeCondition_eq
  [Fintype E]
  {φ : E → Bool → ℝ} :
-- imply
  FKGLatticeCondition (pweight φ) := by
-- proof
  apply StatMech.pweight_fkgLatticeCondition φ

/--
[wprob_fkg_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma wprob_fkg_pos_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  wprob φ A * wprob φ B ≤ wprob φ (A ∩ B) := by
-- proof
  apply StatMech.wprob_fkg_pos φ hφ0 hφ1 hA hB

/--
[wprob_fkg_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma wprob_fkg_neg_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  wprob φ (A ∩ B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.wprob_fkg_neg φ hφ0 hφ1 hA hB

/--
[occursOn_support_of_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma occursOn_support_of_increasing_eq
  {A : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hA : IsIncreasing A)
  (hω : ω ∈ A) :
-- imply
  OccursOn A {e | ω e = true} ω := by
-- proof
  apply StatMech.occursOn_support_of_increasing hA hω

/--
[occursOn_cosupport_of_decreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma occursOn_cosupport_of_decreasing_eq
  {B : Set (ConfigSpace E)}
  {ω : ConfigSpace E}
-- given
  (hB : IsDecreasing B)
  (hω : ω ∈ B) :
-- imply
  OccursOn B {e | ω e = false} ω := by
-- proof
  apply StatMech.occursOn_cosupport_of_decreasing hB hω

/--
[disjoint_support_cosupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma disjoint_support_cosupport_eq
  {ω : ConfigSpace E} :
-- imply
  Disjoint ({e | ω e = true} : Set E) {e | ω e = false} := by
-- proof
  apply StatMech.disjoint_support_cosupport ω

/--
[disjointOccurrence_eq_inter_of_mixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma disjointOccurrence_eq_inter_of_mixed_eq
  {A B : Set (ConfigSpace E)}
-- given
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  disjointOccurrence A B = A ∩ B := by
-- proof
  apply StatMech.disjointOccurrence_eq_inter_of_mixed hA hB

/--
[reimerMixed_wprob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma reimerMixed_wprob_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
-- given
  (hφ0 : ∀ x b, 0 ≤ φ x b)
  (hφ1 : ∀ x, φ x false + φ x true = 1)
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimerMixed_wprob φ hφ0 hφ1 hA hB

/--
[reimerMixed_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterfly.lean)
-/
@[path]
private lemma reimerMixed_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ≥0}
  {A B : Set (ConfigSpace E)}
-- given
  (hp : p ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsDecreasing B) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimerMixed_inequality hp hA hB


-- created on 2026-10-23
