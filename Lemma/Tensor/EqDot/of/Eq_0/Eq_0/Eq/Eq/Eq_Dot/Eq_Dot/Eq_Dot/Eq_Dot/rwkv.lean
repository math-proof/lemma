import Mathlib.LinearAlgebra.Matrix.Notation
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℝ} :
-- imply
  ∀ i j, (if j.1 ≤ i.1 then A i j else A j i) = if i.1 ≤ j.1 then A j i else A i j := by
-- proof
  intro i j
  if hij : i.1 ≤ j.1 then
    if hji : j.1 ≤ i.1 then
      have : i.1 = j.1 := by
        omega
      have hij' : i = j := Fin.ext this
      simp [hij']
    else
      simp [hij, hji]
  else
    have hji : j.1 ≤ i.1 := by
      omega
    simp [hij, hji]


-- created on 2023-06-17
-- updated on 2026-10-26
