import Mathlib
import sympy.Basic


@[main]
private lemma main
  {n : ℕ}
  {s : Finset (Fin n → ℤ)}
-- given
  (hn : 0 < n)
  (hswap : ∀ j : Fin n, ∀ x ∈ s,
    (fun i : Fin n => if i = ⟨0, hn⟩ then x j else if i = j then x ⟨0, hn⟩ else x i) ∈ s)
  (hcard : ∀ x ∈ s, (Finset.univ.image x).card = n) :
-- imply
  s.card = Nat.factorial n * (s.image fun x : Fin n → ℤ => Finset.univ.image x).card := by
-- proof
  sorry


-- created on 2026-10-07
