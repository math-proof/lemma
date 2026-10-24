import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.EKGSequence


namespace MetaMathlibExt

/--
[ekg_a0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EKGSequence.lean)
-/
@[path]
lemma ekg_a0
  {a : ℕ → ℕ}
-- given
  (h : IsEKGSequence a) :
-- imply
  a 0 = 1 := by
-- proof
  obtain ⟨h0, _, _⟩ := h
  exact h0

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ekg_a1](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EKGSequence.lean)
-/
@[path]
lemma ekg_a1
  {a : ℕ → ℕ}
-- given
  (h : IsEKGSequence a) :
-- imply
  a 1 = 2 := by
-- proof
  obtain ⟨_, h1, _⟩ := h
  exact h1

end MetaMathlibExt

namespace MetaMathlibExt

/--
[ekg_a2](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EKGSequence.lean)
-/
@[path]
lemma ekg_a2
  {a : ℕ → ℕ}
-- given
  (h : IsEKGSequence a) :
-- imply
  a 2 = 4 := by
-- proof
  obtain ⟨h0, h1, hspec⟩ := h
  have spec0 := hspec 0
  have e2 : (0 : ℕ) + 2 = 2 := by decide
  have e1 : (0 : ℕ) + 1 = 1 := by decide
  rw [e2] at spec0
  rw [e1] at spec0
  obtain ⟨hpos, hunused, hgcd, hmin⟩ := spec0
  have hlt0 : (0 : ℕ) < 2 := by decide
  have hlt1 : (1 : ℕ) < 2 := by decide
  have hne0 : a 0 ≠ a 2 := hunused 0 hlt0
  have hne1 : a 1 ≠ a 2 := hunused 1 hlt1
  rw [h0] at hne0
  rw [h1] at hne1
  have hne_1 : a 2 ≠ 1 := fun heq => hne0 heq.symm
  have hne_2 : a 2 ≠ 2 := fun heq => hne1 heq.symm
  have hgcd2 : Nat.gcd (a 1) (a 2) > 1 := hgcd
  rw [h1] at hgcd2
  have hunused4 : ∀ i : ℕ, i < 2 → a i ≠ 4 := by
    intro i hi
    have hi01 : i = 0 ∨ i = 1 := by omega
    cases hi01 with
    | inl hh => rw [hh, h0]; decide
    | inr hh => rw [hh, h1]; decide
  have hgcd14 : Nat.gcd (a 1) 4 > 1 := by rw [h1]; decide
  have hle4 : a 2 ≤ 4 := hmin 4 (by decide) hunused4 hgcd14
  have hne_3 : a 2 ≠ 3 := by
    intro heq
    rw [heq] at hgcd2
    have hgcd23 : Nat.gcd 2 3 = 1 := by decide
    omega
  omega

end MetaMathlibExt


-- created on 2026-10-23
