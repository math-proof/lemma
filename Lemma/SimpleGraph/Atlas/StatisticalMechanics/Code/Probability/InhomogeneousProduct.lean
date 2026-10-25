import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
open MeasureTheory ProbabilityTheory Set StatMech StatMech.inhomBernoulliProductMeasure


/--
[bernoulliMeasure_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma bernoulliMeasure_congr_eq
  {p q : ℝ≥0}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (h : p = q) :
-- imply
  bernoulliMeasure p hp = bernoulliMeasure q hq := by
-- proof
  apply StatMech.bernoulliMeasure_congr hp hq h

/--
[apply_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma apply_singleton_eq
  {p : E → ℝ≥0}
  {hp : ∀ e, p e ≤ 1}
  [Fintype E]
  {omega : ConfigSpace E} :
-- imply
  inhomBernoulliProductMeasure p hp {omega} = ∏ e, bernoulliMeasure (p e) (hp e) {omega e} := by
-- proof
  apply StatMech.inhomBernoulliProductMeasure.apply_singleton omega

/--
[real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma real_singleton_eq
  {p : E → ℝ≥0}
  {hp : ∀ e, p e ≤ 1}
  [Fintype E]
  {omega : ConfigSpace E} :
-- imply
  (inhomBernoulliProductMeasure p hp).real {omega} = ∏ e, (bernoulliMeasure (p e) (hp e)).real {omega e} := by
-- proof
  apply StatMech.inhomBernoulliProductMeasure.real_singleton omega

/--
[real_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma real_eq_sum_eq
  {p : E → ℝ≥0}
  {hp : ∀ e, p e ≤ 1}
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)} :
-- imply
  (inhomBernoulliProductMeasure p hp).real A = ∑ omega : ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) omega * (inhomBernoulliProductMeasure p hp).real {omega} := by
-- proof
  apply StatMech.inhomBernoulliProductMeasure.real_eq_sum A

/--
[inhom_real_eq_wprob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_real_eq_wprob_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  (inhomBernoulliProductMeasure p hp).real A = wprob (fun e b => (bernoulliMeasure (p e) (hp e)).real {b}) A := by
-- proof
  apply StatMech.inhom_real_eq_wprob p hp A

/--
[inhom_bk_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_bk_inequality_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1)
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) ≤ (inhomBernoulliProductMeasure p hp).real A * (inhomBernoulliProductMeasure p hp).real B := by
-- proof
  apply StatMech.inhom_bk_inequality p hp hA hB

/--
[inhom_realProb_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_realProb_cylinder_eq
  [Countable E]
  [DecidableEq E]
  {F : Finset E}
  {A : Set (ConfigSpace F)}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  (inhomBernoulliProductMeasure p hp).real (MeasureTheory.cylinder F A) = (inhomBernoulliProductMeasure (fun e : F => p e) (fun e => hp e)).real A := by
-- proof
  apply StatMech.inhom_realProb_cylinder p hp F A

/--
[inhom_coord_true_prob](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_coord_true_prob_eq
  [Countable E]
  [DecidableEq E]
  {e : E}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1) :
-- imply
  (inhomBernoulliProductMeasure p hp).real {omega | omega e = true} = (p e : ℝ) := by
-- proof
  apply StatMech.inhom_coord_true_prob p hp e

/--
[inhom_bk_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_bk_of_finite_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1)
  (hAdep : DependsOn A (F : Set E))
  (hBdep : DependsOn B (F : Set E))
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B) :
-- imply
  (inhomBernoulliProductMeasure p hp).real (disjointOccurrence A B) ≤ (inhomBernoulliProductMeasure p hp).real A * (inhomBernoulliProductMeasure p hp).real B := by
-- proof
  apply StatMech.inhom_bk_of_finite_dependsOn p hp F hAdep hBdep hAinc hBinc

/--
[inhom_bk_triple_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_bk_triple_of_finite_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {P Q R : Set (ConfigSpace E)}
  {F : Finset E}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1)
  (hPdep : DependsOn P (F : Set E))
  (hQdep : DependsOn Q (F : Set E))
  (hRdep : DependsOn R (F : Set E))
  (hP : IsIncreasing P)
  (hQ : IsIncreasing Q)
  (hR : IsIncreasing R) :
-- imply
  (inhomBernoulliProductMeasure p hp).real (disjointOccurrence P (disjointOccurrence Q R)) ≤ (inhomBernoulliProductMeasure p hp).real P * (inhomBernoulliProductMeasure p hp).real Q * (inhomBernoulliProductMeasure p hp).real R := by
-- proof
  apply StatMech.inhom_bk_triple_of_finite_dependsOn p hp F hPdep hQdep hRdep hP hQ hR

/--
[inhom_bk_criterion_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/InhomogeneousProduct.lean)
-/
@[path]
private lemma inhom_bk_criterion_of_finite_dependsOn_eq
  [Countable E]
  [DecidableEq E]
  {s : Finset I}
  {P Q R : I → Set (ConfigSpace E)}
  {F : Finset E}
  {C : Set (ConfigSpace E)}
-- given
  (p : E → ℝ≥0)
  (hp : ∀ e, p e ≤ 1)
  (hPdep : ∀ i ∈ s, DependsOn (P i) (F : Set E))
  (hQdep : ∀ i ∈ s, DependsOn (Q i) (F : Set E))
  (hRdep : ∀ i ∈ s, DependsOn (R i) (F : Set E))
  (hP : ∀ i ∈ s, IsIncreasing (P i))
  (hQ : ∀ i ∈ s, IsIncreasing (Q i))
  (hR : ∀ i ∈ s, IsIncreasing (R i))
  (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
-- imply
  (inhomBernoulliProductMeasure p hp).real C ≤ ∑ i ∈ s, (inhomBernoulliProductMeasure p hp).real (P i) * (inhomBernoulliProductMeasure p hp).real (Q i) * (inhomBernoulliProductMeasure p hp).real (R i) := by
-- proof
  apply StatMech.inhom_bk_criterion_of_finite_dependsOn p hp s P Q R F hPdep hQdep hRdep hP hQ hR hC


-- created on 2026-10-23
