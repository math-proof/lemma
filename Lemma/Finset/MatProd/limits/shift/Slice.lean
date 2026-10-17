import Mathlib.Data.Matrix.Mul
import sympy.Basic


@[path]
private lemma main
  {m : ℕ}
  {f : ℕ → Matrix (Fin m) (Fin m) ℝ}
  {i n : ℕ}
-- given
  (h₀ : i < n) :
-- imply
  ((List.range (n + 1 - i)).map fun k => f (i + k)).prod
    = f i * ((List.range (n - i)).map fun k => f (i + 1 + k)).prod := by
-- proof
  have hlen : n + 1 - i = (n - i) + 1 := by omega
  rw [hlen]
  have hstep : ∀ p : ℕ, ((List.range (p + 1)).map fun k => f (i + k)).prod =
    f i * ((List.range p).map fun k => f (i + 1 + k)).prod := by
    intro p
    induction p with
    | zero =>
      simp
    | succ p ih =>
      rw [List.range_succ, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_singleton]
      have htail : ((List.range (p + 1)).map fun k => f (i + 1 + k)).prod =
        ((List.range p).map fun k => f (i + 1 + k)).prod * f (i + 1 + p) := by
        rw [List.range_succ, List.map_append, List.map_singleton, List.prod_append, List.prod_singleton]
      rw [htail, mul_assoc]
      have : i + (p + 1) = i + 1 + p := by omega
      rw [this]
  rw [hstep (n - i)]


-- created on 2026-10-11
-- updated on 2026-10-17
