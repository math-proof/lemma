import Mathlib
import sympy.Basic
import Theorem.Analysis.NormedSpace.BartleGraves

/--
[bartle_graves](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/BartleGraves.lean)
-/
@[path]
private lemma bartle_graves_eq
-- given
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (T : E →L[ℝ] F)
  (hT : Function.Surjective T) :
-- imply
  ∃ (g : F → E) (C : ℝ), 0 ≤ C ∧ Continuous g ∧ (∀ y, T (g y) = y) ∧ g 0 = 0 ∧
    (∀ (t : ℝ) (y : F), 0 ≤ t → g (t • y) = t • g y) ∧
    (∀ y, ‖g y‖ ≤ C * ‖y‖) := by
-- proof
  apply FunctionalAnalysis.BartleGravesWanted.bartle_graves T hT

-- created on 2026-10-10
