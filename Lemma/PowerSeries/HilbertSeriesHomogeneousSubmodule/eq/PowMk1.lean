import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.PowerSeries.FinrankHomogeneousSubmodule.eq.Multichoose
open MvPolynomial PowerSeries


/--
Atlas `hilbertSeries_homogeneousSubmodule` with `hilbertSeries` unfolded
(`SyzygiesKoszul` olean broken).

[hilbertSeries_homogeneousSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  [Field k]
  {n : ℕ} :
-- imply
  mk (fun i => (Module.finrank k (homogeneousSubmodule (Fin n) k i) : ℤ)) =
    (mk (1 : ℕ → ℤ)) ^ n := by
-- proof
  cases n with
  | zero =>
    ext d
    simp only [coeff_mk, pow_zero, PowerSeries.coeff_one]
    rw [FinrankHomogeneousSubmodule.eq.Multichoose]
    cases d <;> simp
  | succ n =>
    ext d
    rw [show mk (1 : ℕ → ℤ) = (mk 1 : PowerSeries ℤ) by rfl]
    rw [mk_one_pow_eq_mk_choose_add]
    simp only [coeff_mk]
    rw [FinrankHomogeneousSubmodule.eq.Multichoose]
    congr 1
    rw [Nat.multichoose_eq]
    rw [show n + 1 + d - 1 = n + d by omega]
    exact Nat.choose_symm_of_eq_add (by omega)


-- created on 2026-10-24
