import sympy.Basic


def Fin.toSplit {d : ℕ} (i : Fin (d + d)) : Fin (d + d) :=
  ⟨i / 2 + i % 2 * d, by by_cases (i : ℕ) % 2 = 0 <;> grind⟩


@[main]
private lemma main
-- given
  (i : Fin (d + d)) :
-- imply
  i.toSplit =
    if (i : ℕ) % 2 = 0 then
      (i : ℕ) / 2
    else
      (i : ℕ) / 2 + d := by
-- proof
  grind [Fin.toSplit]


-- created on 2026-09-05
