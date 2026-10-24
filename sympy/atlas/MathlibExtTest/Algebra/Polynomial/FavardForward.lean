/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Polynomial/FavardForward.lean -/

/-
Author: @akiezun, Avocado
-/

import Lemma.Int.Polynomial.FavardForward


namespace MetaMathlibExt

variable {R : Type*} [Field R]

/-- The recurrence coefficients returned by `favard_forward` are nonzero
at every positive index. -/
example (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal p) :
    ∃ β : ℕ → R, ∀ n, β (n + 1) ≠ 0 := by
  obtain ⟨_, β, hβ, _, _, _⟩ := favard_forward p hmonic horth
  exact ⟨β, hβ⟩

/-- First initial condition: the family starts at `1`. -/
example (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal p) :
    p 0 = 1 := by
  obtain ⟨_, _, _, h0, _, _⟩ := favard_forward p hmonic horth
  exact h0

/-- Second initial condition: `p 1` is determined by the first shift. -/
example (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal p) :
    ∃ α : ℕ → R, p 1 = Polynomial.X - Polynomial.C (α 0) := by
  obtain ⟨α, _, _, _, h1, _⟩ := favard_forward p hmonic horth
  exact ⟨α, h1⟩

/-- General three-term recurrence at every level. -/
example (p : ℕ → Polynomial R)
    (hmonic : ∀ n, (p n).Monic)
    (horth : Polynomial.IsFormallyOrthogonal p) :
    ∃ α β : ℕ → R, ∀ n, p (n + 2) =
      (Polynomial.X - Polynomial.C (α (n + 1))) * p (n + 1) -
        Polynomial.C (β (n + 1)) * p n := by
  obtain ⟨α, β, _, _, _, hrec⟩ := favard_forward p hmonic horth
  exact ⟨α, β, hrec⟩

end MetaMathlibExt
