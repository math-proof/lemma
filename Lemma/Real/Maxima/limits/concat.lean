import Mathlib.Data.Finset.Lattice.Fold
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {f : ℤ → ℝ} {a b c : ℤ}
  (h₀ : a ≤ b)
  (h₁ : b < c) :
-- imply
  (Finset.Icc a c).sup' (Finset.nonempty_Icc.2 (h₀.trans h₁.le)) f =
    max ((Finset.Icc a b).sup' (Finset.nonempty_Icc.2 h₀) f)
      ((Finset.Icc (b + 1) c).sup' (Finset.nonempty_Icc.2 h₁) f) := by
-- proof
  have hunion : Finset.Icc a b ∪ Finset.Icc (b + 1) c = Finset.Icc a c := by
    ext k
    simp [Finset.mem_Icc]
    omega
  have hne₂ : (Finset.Icc (b + 1) c).Nonempty := by
    rw [Finset.nonempty_Icc]
    omega
  simpa [hunion] using
    (Finset.sup'_union (Finset.nonempty_Icc.2 h₀) hne₂ f)


-- created on 2023-11-18
-- updated on 2026-10-26
