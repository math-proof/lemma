import sympy.Basic


def Fin.ofSplit {d : ℕ} (k : Fin (d + d)) : Fin (d + d) :=
  ⟨2 * (k % d) + k / d, by
    have := k.isLt
    have hd : 0 < d := by
      omega
    have := Nat.mod_lt (k : ℕ) hd
    have : (k : ℕ) / d < 2 := Nat.div_lt_of_lt_mul (by omega)
    omega⟩


@[main]
private lemma main
-- given
  (k : Fin (d + d)) :
-- imply
  (Fin.ofSplit k : ℕ) =
    if (k : ℕ) < d then
      2 * (k : ℕ)
    else
      2 * (k - d) + 1 := by
-- proof
  dsimp [Fin.ofSplit]
  if h : (k : ℕ) < d then
    rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]
    simp [h]
  else
    have hdiv : (k : ℕ) / d = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    grind [Nat.mod_eq_sub_mul_div]


-- created on 2026-09-05
