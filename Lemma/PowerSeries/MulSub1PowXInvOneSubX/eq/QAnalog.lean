import Mathlib
import sympy.Basic
open PowerSeries


/--
Atlas `one_sub_X_pow_mul_invOneSubX` with `invOneSubX = mk (fun _ => 1)` and
`qAnalog d = mk (fun i => if i < d then 1 else 0)` (SyzygiesKoszul olean broken).

[one_sub_X_pow_mul_invOneSubX](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {d : ℕ} :
-- imply
  (1 - (X : PowerSeries ℤ) ^ d) * mk (fun _ => (1 : ℤ)) =
    mk (fun i => if i < d then (1 : ℤ) else 0) := by
-- proof
  ext m
  simp only [coeff_mk, sub_mul, one_mul, map_sub, coeff_X_pow_mul']
  if hm : m < d then
    have : ¬d ≤ m := Nat.not_le_of_gt hm
    simp [hm, this]
  else
    have hle : d ≤ m := Nat.le_of_not_gt hm
    simp [hm, hle]


-- created on 2026-10-24
