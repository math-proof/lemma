import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_nomonotoneloop
open Finset StatMech StatMech.Walls


/--
[kc_abs_diff_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_abs_diff_one_eq
  {g : ℕ → ℤ}
  {i : ℕ} :
-- imply
  |g (i + 1) - g i| = 1 ↔ (g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1) := by
-- proof
  apply StatMech.Walls.kc_abs_diff_one g i

/--
[kc_max_neighbours_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_max_neighbours_eq_eq
  {g : ℕ → ℤ}
  {L : ℕ}
  {m : ℕ}
-- given
  (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
  (hm0 : 0 < m)
  (hmL : m < L)
  (hmmax : ∀ i, i ≤ L → g i ≤ g m) :
-- imply
  g (m - 1) = g (m + 1) := by
-- proof
  apply StatMech.Walls.kc_max_neighbours_eq g L hstep hm0 hmL hmmax

/--
[kc_min_neighbours_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_min_neighbours_eq_eq
  {g : ℕ → ℤ}
  {L : ℕ}
  {m : ℕ}
-- given
  (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
  (hm0 : 0 < m)
  (hmL : m < L)
  (hmmin : ∀ i, i ≤ L → g m ≤ g i) :
-- imply
  g (m - 1) = g (m + 1) := by
-- proof
  apply StatMech.Walls.kc_min_neighbours_eq g L hstep hm0 hmL hmmin

/--
[kc_no_monotone_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_no_monotone_loop_eq
  {g : ℕ → ℤ}
  {L : ℕ}
-- given
  (h3 : 3 ≤ L)
  (hloop : g 0 = g L)
  (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
  (hne : g 1 ≠ g 0)
  (hinj : Set.InjOn g {i | i ≤ L - 1}) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.kc_no_monotone_loop g L h3 hloop hstep hne hinj

/--
[kc_no_monotone_loop_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_no_monotone_loop_abs_eq
  {g : ℕ → ℤ}
  {L : ℕ}
-- given
  (h3 : 3 ≤ L)
  (hloop : g 0 = g L)
  (hstep : ∀ i, i < L → |g (i + 1) - g i| = 1)
  (hne : g 1 ≠ g 0)
  (hinj : Set.InjOn g {i | i ≤ L - 1}) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.kc_no_monotone_loop_abs g L h3 hloop hstep hne hinj

/--
[kc_eaw_no_monotone_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_eaw_no_monotone_loop_eq
  {g : ℕ → ℤ}
  {L : ℕ}
-- given
  (h3 : 3 ≤ L)
  (hloop : g 0 = g L)
  (hstep : ∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1)
  (hne : g 1 ≠ g 0)
  (hinj : Set.InjOn g {i | i ≤ L - 1}) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.kc_eaw_no_monotone_loop g L h3 hloop hstep hne hinj

/--
[kc_no_monotone_loop_iff_eaw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_nomonotoneloop.lean)
-/
@[path]
private lemma kc_no_monotone_loop_iff_eaw_eq :
-- imply
  (∀ (g : ℕ → ℤ) (L : ℕ), 3 ≤ L → g 0 = g L → (∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1) → g 1 ≠ g 0 → Set.InjOn g {i | i ≤ L - 1} → False) ↔ (∀ (g : ℕ → ℤ) (L : ℕ), 3 ≤ L → g 0 = g L → (∀ i, i < L → g (i + 1) = g i + 1 ∨ g (i + 1) = g i - 1) → g 1 ≠ g 0 → Set.InjOn g {i | i ≤ L - 1} → False) := by
-- proof
  apply StatMech.Walls.kc_no_monotone_loop_iff_eaw


-- created on 2026-10-23
