import Mathlib
import sympy.Basic
import Lemma.PowerSeries.FinrankHomogeneousSubmodule.eq.MultichoosePrime
open MvPolynomial PowerSeries


/--
Atlas `hilbert_series_polynomial_ring` with `hilbertSeries` / `invOneSubX` unfolded
(`SyzygiesKoszul` olean broken).

[hilbert_series_polynomial_ring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ} :
-- imply
  mk (fun i => (Module.finrank k (homogeneousSubmodule (Fin n) k i) : ℤ)) =
    mk (fun _ => (1 : ℤ)) ^ n := by
-- proof
  ext d
  simp only [coeff_mk, coeff_pow, Finset.prod_const_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, FinrankHomogeneousSubmodule.eq.MultichoosePrime]
  norm_cast
  rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_range]


-- created on 2026-10-24
