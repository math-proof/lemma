import Mathlib.Data.Finset.Lattice.Fold
import sympy.Basic


@[path]
private lemma main
  {f : ℤ → ℝ} {i n : ℤ}
  (h₀ : i ≤ n) :
-- imply
  (Finset.Icc i n).inf' (Finset.nonempty_Icc.2 h₀) f =
    if h : i = n then f i
    else min (f i) ((Finset.Icc (i + 1) n).inf' (Finset.nonempty_Icc.2 (by omega)) f) := by
-- proof
  if h : i = n then
    simp [h, Finset.Icc_self, Finset.inf'_singleton]
  else
    have hinsert : insert i (Finset.Icc (i + 1) n) = Finset.Icc i n := by
      ext k
      simp [Finset.mem_Icc]
      omega
    simp [h]
    simpa [hinsert] using
      (Finset.inf'_insert (s := Finset.Icc (i + 1) n)
        (H := Finset.nonempty_Icc.2 (by omega)) (b := i) (f := f))


-- created on 2020-12-18
-- updated on 2026-10-17
