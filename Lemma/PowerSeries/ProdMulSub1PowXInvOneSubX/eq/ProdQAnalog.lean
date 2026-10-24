import Mathlib
import sympy.Basic
import Lemma.PowerSeries.MulSub1PowXInvOneSubX.eq.QAnalog
open PowerSeries


/--
Atlas `prod_one_sub_mul_invOneSubX_eq_prod_qAnalog` with `invOneSubX = mk (fun _ => 1)` and
`qAnalog` unfolded (SyzygiesKoszul olean broken).

[prod_one_sub_mul_invOneSubX_eq_prod_qAnalog](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  {d : Fin m → ℕ} :
-- imply
  (∏ i : Fin m, (1 - (X : PowerSeries ℤ) ^ d i)) * mk (fun _ => (1 : ℤ)) ^ m =
    ∏ i : Fin m, mk (fun j => if j < d i then (1 : ℤ) else 0) := by
-- proof
  have h1 : mk (fun _ => (1 : ℤ)) ^ m = ∏ _ : Fin m, mk (fun _ => (1 : ℤ)) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact MulSub1PowXInvOneSubX.eq.QAnalog (d := d i)


-- created on 2026-10-24
