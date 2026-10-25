/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QuadraticForms/Reduced.lean -/

import Def.NumberTheory.QuadraticForms.Reduced
import Lemma.Nat.QuadraticForms.Reduced
/-!
# Tests for `BinaryQuadraticForm.IsGaussReduced`
Boundary coverage for Mortenson arXiv:1702.01627v2 Section 2 line 259.
-/


namespace BinaryQuadraticForm.IsGaussReducedTest

-- Accept (1,1,1): positive middle coefficient, both equalities active
example : BinaryQuadraticForm.IsGaussReduced 1 1 1 := by
  unfold BinaryQuadraticForm.IsGaussReduced
  decide

-- Accept (1,0,1): zero middle coefficient, frozen requirement
example : BinaryQuadraticForm.IsGaussReduced 1 0 1 := by
  unfold BinaryQuadraticForm.IsGaussReduced
  decide

-- Reject (1,-1,1): tie-break violation; establish every non-tie-break conjunct
example : 0 < (1 : ℤ) := by decide

example : discrim (1 : ℤ) (-1) 1 < 0 := by decide

example : |( -1 : ℤ)| ≤ 1 := by decide

example : (1 : ℤ) ≤ 1 := by decide

example : |( -1 : ℤ)| = (1 : ℤ) ∨ (1 : ℤ) = 1 := by decide

example : ¬ BinaryQuadraticForm.IsGaussReduced 1 (-1) 1 := by
  unfold BinaryQuadraticForm.IsGaussReduced
  decide

-- Reject non-positive-definite (0,0,1): fails 0 < a
example : ¬ BinaryQuadraticForm.IsGaussReduced 0 0 1 := by
  unfold BinaryQuadraticForm.IsGaussReduced
  decide

example : ¬ (0 : ℤ) > 0 := by decide

-- Isolate |b|=a branch with a < c: (1,-1,2) non-reduced only by first equality
example : |( -1 : ℤ)| = (1 : ℤ) := by decide

example : ¬ (1 : ℤ) = 2 := by decide

example : |( -1 : ℤ)| ≤ (1 : ℤ) ∧ (1 : ℤ) ≤ 2 ∧
    discrim (1 : ℤ) (-1) 2 < 0 ∧ 0 < (1 : ℤ) := by decide

example : ¬ BinaryQuadraticForm.IsGaussReduced 1 (-1) 2 := by
  unfold BinaryQuadraticForm.IsGaussReduced
  decide

-- Isolate a=c branch with strict |b| < a: (2,-1,2) non-reduced only by second equality
example : |( -1 : ℤ)| < (2 : ℤ) := by decide

example : ¬ |( -1 : ℤ)| = (2 : ℤ) := by decide

example : (2 : ℤ) = 2 := by decide

example : |( -1 : ℤ)| ≤ (2 : ℤ) ∧ (2 : ℤ) ≤ 2 ∧
    discrim (2 : ℤ) (-1) 2 < 0 ∧ 0 < (2 : ℤ) := by decide

example : ¬ BinaryQuadraticForm.IsGaussReduced 2 (-1) 2 := by
  unfold BinaryQuadraticForm.IsGaussReduced
  decide

-- Bridge: reduced implies loose signed bounds via _root_.abs_le
example (a b c : ℤ) (h : BinaryQuadraticForm.IsGaussReduced a b c) :
    -a ≤ b ∧ b ≤ a :=
  h.loose_bounds

end BinaryQuadraticForm.IsGaussReducedTest
