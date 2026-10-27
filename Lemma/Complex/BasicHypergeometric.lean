import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.BasicHypergeometric

open MetaMathlibExt.BasicHypergeometric

/--
[BasicHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/BasicHypergeometric.lean)
-/
@[path]
private lemma basic_hypergeometric_coefficient_zero_eq
-- given
  (r s : ℕ)
  (a : Fin r → ℂ)
  (b : Fin s → ℂ)
  (q : ℂ) :
-- imply
  basicHypergeometricCoefficient a b q 0 = 1 := by
-- proof
  apply MetaMathlibExt.BasicHypergeometric.basicHypergeometricCoefficient_zero a b q

/--
[BasicHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/BasicHypergeometric.lean)
-/
@[path]
private lemma coeff_basic_hypergeometric_series_eq
-- given
  (r s : ℕ)
  (a : Fin r → ℂ)
  (b : Fin s → ℂ)
  (q : ℂ)
  (n : ℕ) :
-- imply
  PowerSeries.coeff n (basicHypergeometricSeries a b q) =
    basicHypergeometricCoefficient a b q n := by
-- proof
  apply MetaMathlibExt.BasicHypergeometric.coeff_basicHypergeometricSeries a b q n

/--
[BasicHypergeometric](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/BasicHypergeometric.lean)
-/
@[path]
private lemma basic_hypergeometric_coefficient_phi_succ_eq
-- given
  (s : ℕ)
  (a : Fin (s + 1) → ℂ)
  (b : Fin s → ℂ)
  (q : ℂ)
  (n : ℕ) :
-- imply
  basicHypergeometricCoefficient a b q n =
    (∏ i, ∏ j ∈ Finset.range n, (1 - a i * q ^ j)) /
      ((∏ j ∈ Finset.range n, (1 - q ^ (j + 1))) *
        ∏ i, ∏ j ∈ Finset.range n, (1 - b i * q ^ j)) := by
-- proof
  apply MetaMathlibExt.BasicHypergeometric.basicHypergeometricCoefficient_phi_succ s a b q n

-- created on 2026-10-10
