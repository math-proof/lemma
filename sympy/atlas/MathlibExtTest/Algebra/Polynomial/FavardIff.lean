/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/FavardIff.lean -/

/-
Author: @akiezun, Avocado
-/

import Lemma.Int.Polynomial.FavardIff


namespace MetaMathlibExt

variable {R : Type*} [Field R]

/-- Forward projection: a formally orthogonal monic family satisfies a three-term recurrence
with nonzero `β`. -/
example (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal p) :
    ∃ β : ℕ → R, ∀ n, β (n + 1) ≠ 0 := by
  obtain ⟨_, β, hβ, _⟩ := (favard_iff p hmonic).mp horth
  exact ⟨β, hβ⟩

/-- Reverse projection: recurrence data with nonzero `β` yields formal orthogonality. -/
example (p : ℕ → Polynomial R) (α β : ℕ → R)
    (hmonic : ∀ n, (p n).Monic)
    (hβ : ∀ n, β (n + 1) ≠ 0) (h0 : p 0 = 1)
    (h1 : p 1 = Polynomial.X - Polynomial.C (α 0))
    (hrec : ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
      p (n + 1) - Polynomial.C (β (n + 1)) * p n) :
    Polynomial.IsFormallyOrthogonal p :=
  (favard_iff p hmonic).mpr ⟨α, β, hβ, h0, h1, hrec⟩

/-- Consuming the reverse implication: the orthogonalizing functional vanishes on `p n * p m`
for `n ≠ m` and each `p n` has degree `n`. -/
example (p : ℕ → Polynomial R) (α β : ℕ → R)
    (hmonic : ∀ n, (p n).Monic)
    (hβ : ∀ n, β (n + 1) ≠ 0) (h0 : p 0 = 1)
    (h1 : p 1 = Polynomial.X - Polynomial.C (α 0))
    (hrec : ∀ n, p (n + 2) = (Polynomial.X - Polynomial.C (α (n + 1))) *
      p (n + 1) - Polynomial.C (β (n + 1)) * p n) :
    ∃ L : Polynomial R →ₗ[R] R, (p 2).natDegree = 2 ∧ L (p 0 * p 1) = 0 ∧ L (p 1 ^ 2) ≠ 0 := by
  obtain ⟨L, hdeg, horth, hnorm⟩ := (favard_iff p hmonic).mpr ⟨α, β, hβ, h0, h1, hrec⟩
  exact ⟨L, hdeg 2, horth 0 1 (by decide), hnorm 1⟩

end MetaMathlibExt
