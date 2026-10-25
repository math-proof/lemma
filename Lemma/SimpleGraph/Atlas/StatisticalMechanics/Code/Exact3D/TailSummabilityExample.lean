import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
open StatMech StatMech.Exact3D StatMech.Exact3D.TailSummabilityExample


/--
[exampleSplit_additive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean)
-/
@[path]
private lemma exampleSplit_additive_eq :
-- imply
  exampleSplit.Additive := by
-- proof
  apply StatMech.Exact3D.TailSummabilityExample.exampleSplit_additive

/--
[exampleFiniteTableUpperBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean)
-/
@[path]
private lemma exampleFiniteTableUpperBound_eq :
-- imply
  FiniteTableUpperBound exampleTable exampleClassifier exampleSplit.finiteContribution 1 where covers := by
-- proof
  apply StatMech.Exact3D.TailSummabilityExample.exampleFiniteTableUpperBound

/--
[exampleTailEnvelopeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean)
-/
@[path]
private lemma exampleTailEnvelopeOn_eq :
-- imply
  exampleSplit.TailEnvelopeOn (Finset.univ : Finset (Fin 2)) (fun _ => (1 : ℝ) / 10) := by
-- proof
  apply StatMech.Exact3D.TailSummabilityExample.exampleTailEnvelopeOn

/--
[exampleTailEnvelopeSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean)
-/
@[path]
private lemma exampleTailEnvelopeSum_le_eq :
-- imply
  (∑ _a ∈ (Finset.univ : Finset (Fin 2)), ((1 : ℝ) / 10)) ≤ (1 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.TailSummabilityExample.exampleTailEnvelopeSum_le

/--
[exampleTotal_zero_off_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean)
-/
@[path]
private lemma exampleTotal_zero_off_support_eq :
-- imply
  ∀ a : Fin 2, a ∉ (Finset.univ : Finset (Fin 2)) → exampleSplit.totalContribution a = 0 := by
-- proof
  apply StatMech.Exact3D.TailSummabilityExample.exampleTotal_zero_off_support

/--
[example_tsum_total_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/TailSummabilityExample.lean)
-/
@[path]
private lemma example_tsum_total_le_eq :
-- imply
  (∑' a : Fin 2, exampleSplit.totalContribution a) ≤ ((Finset.univ : Finset (Fin 2)).card : ℝ) * 1 + (1 : ℝ) / 5 := by
-- proof
  apply StatMech.Exact3D.TailSummabilityExample.example_tsum_total_le


-- created on 2026-10-23
