import Mathlib
import sympy.Basic
import sympy.Analysis.Calculus.EulerMaclaurinFormula

/--
[eulerMaclaurinFormula](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Calculus/EulerMaclaurinFormula.lean)
-/
@[path]
private lemma eulerMaclaurinFormula_eq
-- given
  (a b : ℤ) (p : ℕ) (f : ℝ → ℝ)
  (hab : a < b) (hp : 1 ≤ p) (hdf : ContDiffOn ℝ (↑p) f (Set.Icc (↑a) (↑b))) :
-- imply
  ∃ P : ℕ → ℝ → ℝ,
    (∀ (m : ℕ) (x : ℝ), P m (x + 1) = P m x) ∧
    (∀ x ∈ Set.Ico (0 : ℝ) 1, P p x =
      ∑ j ∈ Finset.range (p + 1), (Nat.choose p j : ℝ) *
        (if j = 1 then (-1 / 2 : ℝ) else (bernoulli j : ℝ)) * x ^ (p - j)) ∧
    ∑ n ∈ Finset.Icc a b, f (↑n) =
      (∫ x in (↑a)..(↑b), f x) + (f (↑a) + f (↑b)) / 2 +
        (∑ k ∈ Finset.Icc 1 (p / 2),
          (bernoulli (2 * k) : ℝ) / (Nat.factorial (2 * k) : ℝ) *
            (iteratedDerivWithin (2 * k - 1) f (Set.Icc (↑a) (↑b)) (↑b) -
              iteratedDerivWithin (2 * k - 1) f (Set.Icc (↑a) (↑b)) (↑a))) +
        ((-1 : ℝ) ^ (p + 1) / (Nat.factorial p : ℝ) *
          (∫ x in (↑a)..(↑b), P p x * iteratedDerivWithin p f (Set.Icc (↑a) (↑b)) x)) := by
-- proof
  apply Real.Calculus.EulerMaclaurinFormula.eulerMaclaurinFormula a b p f hab hp hdf


-- created on 2026-10-09
