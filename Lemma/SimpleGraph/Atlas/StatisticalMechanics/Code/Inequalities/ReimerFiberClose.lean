import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerFiberClose.Part2
open MeasureTheory Finset StatMech


/--
[DeterminedBy.mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma mono_eq
  {A : Set (ConfigSpace E)}
  {K K' : Set E}
-- given
  (hKK' : K ⊆ K')
  (h : DeterminedBy A K) :
-- imply
  DeterminedBy A K' := by
-- proof
  apply StatMech.DeterminedBy.mono hKK' h

/--
[determinedBy_occursOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma determinedBy_occursOn_eq
  {A : Set (ConfigSpace E)}
  {K : Set E}
  {ω : ConfigSpace E}
-- given
  (h : DeterminedBy A K)
  (hω : ω ∈ A) :
-- imply
  OccursOn A K ω := by
-- proof
  apply StatMech.determinedBy_occursOn h hω

/--
[disjointOccurrence_eq_inter_of_determined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma disjointOccurrence_eq_inter_of_determined_eq
  {A B : Set (ConfigSpace E)}
  {K L : Set E}
-- given
  (hKL : Disjoint K L)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  disjointOccurrence A B = A ∩ B := by
-- proof
  apply StatMech.disjointOccurrence_eq_inter_of_determined hKL hA hB

/--
[wprob_inter_eq_mul_predicate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma wprob_inter_eq_mul_predicate_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  [DecidablePred p]
  {φ : E → Bool → ℝ}
-- given
  (p : E → Prop)
  (h0 : ∀ x, φ x false + φ x true = 1)
  (hA : DeterminedBy A {x | p x})
  (hB : DeterminedBy B {x | ¬ p x}) :
-- imply
  wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
-- proof
  apply StatMech.wprob_inter_eq_mul_predicate A B p φ h0 hA hB

/--
[wprob_inter_eq_mul_of_determined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma wprob_inter_eq_mul_of_determined_eq
  [Fintype E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {K L : Set E}
  {φ : E → Bool → ℝ}
-- given
  (hKL : Disjoint K L)
  (h0 : ∀ x, φ x false + φ x true = 1)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  wprob φ (A ∩ B) = wprob φ A * wprob φ B := by
-- proof
  apply StatMech.wprob_inter_eq_mul_of_determined A B hKL φ h0 hA hB

/--
[reimer_wprob_eq_of_determinedDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma reimer_wprob_eq_of_determinedDisjoint_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
  {K L : Set E}
-- given
  (h0 : ∀ x, φ x false + φ x true = 1)
  (hKL : Disjoint K L)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  wprob φ (disjointOccurrence A B) = wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_eq_of_determinedDisjoint φ h0 hKL hA hB

/--
[reimer_wprob_le_of_determinedDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma reimer_wprob_le_of_determinedDisjoint_eq
  [Fintype E]
  [DecidableEq E]
  {φ : E → Bool → ℝ}
  {A B : Set (ConfigSpace E)}
  {K L : Set E}
-- given
  (h0 : ∀ x, φ x false + φ x true = 1)
  (hKL : Disjoint K L)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimer_wprob_le_of_determinedDisjoint φ h0 hKL hA hB

/--
[reimerCore_holds_on_determinedDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma reimerCore_holds_on_determinedDisjoint_eq
  {n : ℕ}
  {φ : Fin n → Bool → ℝ}
  {A B : Set (ConfigSpace (Fin n))}
  {K L : Set (Fin n)}
-- given
  (_hφ0 : ∀ i b, 0 ≤ φ i b)
  (hφ1 : ∀ i, φ i false + φ i true = 1)
  (hKL : Disjoint K L)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  wprob φ (disjointOccurrence A B) ≤ wprob φ A * wprob φ B := by
-- proof
  apply StatMech.reimerCore_holds_on_determinedDisjoint n φ _hφ0 hφ1 A B hKL hA hB

/--
[reimer_bernoulli_eq_of_determinedDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma reimer_bernoulli_eq_of_determinedDisjoint_eq
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A B : Set (ConfigSpace E)}
  {K L : Set E}
-- given
  (hp : p ≤ 1)
  (hKL : Disjoint K L)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) = (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimer_bernoulli_eq_of_determinedDisjoint hp hKL hA hB

/--
[reimer_inequality_determinedDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean)
-/
@[path]
private lemma reimer_inequality_determinedDisjoint_eq
  [Fintype E]
  [DecidableEq E]
  {p : NNReal}
  {A B : Set (ConfigSpace E)}
  {K L : Set E}
-- given
  (hp : p ≤ 1)
  (hKL : Disjoint K L)
  (hA : DeterminedBy A K)
  (hB : DeterminedBy B L) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence A B) ≤ (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.reimer_inequality_determinedDisjoint hp hKL hA hB


-- created on 2026-10-23
