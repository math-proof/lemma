/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry2Corollary1DerivativeSeries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 2, Corollary 1

For `f` analytic on a disc of radius `R > 1` and `z` not a nonpositive integer, the series
`∑ f⁽ᵏ⁾(0) / ((z + k) k!)` and `∑ (-1)ᵏ f⁽ᵏ⁾(1) / (z (z + 1) ⋯ (z + k))` have the same sum,
provided the double series obtained by expanding each `f⁽ʲ⁾(1)` in its Taylor series at `0`
is summable.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry2Corollary1DerivativeSeries

private def sigmaProdEquiv : (Σ _ : ℕ, ℕ) ≃ ℕ × ℕ where
  toFun q := (q.1, q.2)
  invFun p := ⟨p.1, p.2⟩
  left_inv := by
    intro q
    cases q
    rfl
  right_inv := by
    intro p
    cases p
    rfl

private def diagEquiv : (Σ n : ℕ, Fin (n + 1)) ≃ ℕ × ℕ where
  toFun q := (q.2.val, q.1 - q.2.val)
  invFun p := ⟨p.1 + p.2, p.1, by omega⟩
  left_inv := by
    rintro ⟨n, ⟨j, hj⟩⟩
    have hje : j + (n - j) = n := by omega
    change (⟨j + (n - j), (⟨j, by omega⟩ : Fin (j + (n - j) + 1))⟩ : Σ n : ℕ, Fin (n + 1)) =
      ⟨n, ⟨j, hj⟩⟩
    simp only [hje, Sigma.mk.injEq]
    have hIdx : j + (n - j) + 1 = n + 1 := by omega
    exact ⟨trivial, (Fin.heq_ext_iff hIdx).mpr rfl⟩
  right_inv := by
    rintro ⟨u, v⟩
    dsimp only
    rw [Nat.add_sub_cancel_left]
end Entry2Corollary1DerivativeSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
