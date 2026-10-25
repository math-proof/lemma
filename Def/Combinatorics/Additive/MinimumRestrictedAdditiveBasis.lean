/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Range
import Mathlib.Tactic
import Theorem.Combinatorics.Additive.MinimumRestrictedAdditiveBasis


namespace MetaMathlibExt

open Classical in
/-- Minimum restricted additive-basis cardinality for `[0, s]`: the summand
set `A : Finset ℕ` satisfies the restriction `2 * a ≤ s` for all `a ∈ A`;
every `x ≤ s` equals `a + b` for some `a ∈ A`, `b ∈ A` (independent choices,
so `a = b` allowed); `A.card = k` for `opt = some k`, minimal among all such
witness sets; `opt = none` exactly when no such witness set exists. The
restriction `2 * a ≤ s` applies for every `s`, odd or even, with no parity
requirement and no sentinel value for absence.

Source: Jukka Kohonen, Visa Koivunen, and Robin Rajamäki, *Planar Additive
Bases for Rectangles*, Journal of Integer Sequences 21 (2018), Article
18.9.8: additive-basis notion (`A + A ⊇ [0, n]`), lines 126–128;
one-dimensional restricted basis (`A ⊆ [0, n/2]`), lines 170–171; minimum
restricted-basis notation `k^*`, lines 200–203,
<https://cs.uwaterloo.ca/journals/JIS/VOL21/Rajamaki/raj.tex>.
The one-dimensional `k^*(s, 0)` notion supports G. Yu's restricted 2-basis
bound (`s_x / k^*(s_x, 0)^2 ≤ 0.41983`, equation `eq:yu_restr`, lines
897–901), quoting G. Yu, *Upper bounds for finite additive 2-bases*,
Proc. Amer. Math. Soc. 137 (2009), 11–18, Theorem 1.2.

Proves `Wanted` entry `minimumRestrictedAdditiveBasisCard`. -/
noncomputable def minimumRestrictedAdditiveBasisCard (s : Nat) :
    { opt : Option Nat //
      (∀ k : Nat, opt = some k →
        ((∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
          (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x) ∧ A.card = k) ∧
          (∀ B : Finset Nat, (∀ b ∈ B, 2 * b ≤ s) →
            (∀ x : Nat, x ≤ s → ∃ a ∈ B, ∃ b ∈ B, a + b = x) → k ≤ B.card))) ∧
      (opt = none →
        ¬∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
          (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x)) } := by
  by_cases h : ∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
      ∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x
  · have hex : ∃ k, ∃ A : Finset Nat, ((∀ a ∈ A, 2 * a ≤ s) ∧
        (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x)) ∧ A.card = k := by
      obtain ⟨A₀, hA₀⟩ := h
      exact ⟨A₀.card, A₀, hA₀, rfl⟩
    refine ⟨some (Nat.find hex), ?_, ?_⟩
    · intro k hk
      have hk' : Nat.find hex = k := Option.some_inj.mp hk
      subst hk'
      obtain ⟨A, hA, hcard⟩ := Nat.find_spec hex
      obtain ⟨hbound, hcover⟩ := hA
      refine ⟨⟨A, hbound, hcover, hcard⟩, ?_⟩
      intro B hBbound hBcover
      have hmem : ∃ A : Finset Nat, ((∀ a ∈ A, 2 * a ≤ s) ∧
          (∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x)) ∧
          A.card = B.card :=
        ⟨B, ⟨hBbound, hBcover⟩, rfl⟩
      exact Nat.find_min' hex hmem
    · intro hnone
      cases hnone
  · refine ⟨none, ?_, ?_⟩
    · intro k hk
      cases hk
    · intro _ hx
      exact h hx

end MetaMathlibExt
