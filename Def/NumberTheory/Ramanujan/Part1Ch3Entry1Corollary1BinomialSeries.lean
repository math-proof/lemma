/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1Corollary1BinomialSeries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Topology.UniformSpace.Uniformizable
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 1, Corollary 1

Binomial-series specialization of the Q-weighted Taylor-shift identity.
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry1Corollary1BinomialSeries

/-- Reindexing: pairs by (sum, the pair itself with proof). -/
def pairEquiv : ℕ × ℕ ≃ Σ _k : ℕ, {p : ℕ × ℕ // p.1 + p.2 = _k} where
  toFun p := ⟨p.1 + p.2, p, rfl⟩
  invFun q := q.2.1
  left_inv p := by
    obtain ⟨a, b⟩ := p
    rfl
  right_inv q := by
    obtain ⟨k, ⟨p, hp⟩⟩ := q
    cases hp
    rfl

/-- Each fiber is finite. -/
def fiberEquiv (k : ℕ) : {p : ℕ × ℕ // p.1 + p.2 = k} ≃ Fin (k + 1) where
  toFun q := ⟨q.1.1, by
    have hle : q.1.1 ≤ k := by omega
    exact Nat.lt_succ_of_le hle⟩
  invFun j := ⟨(j.1, k - j.1), by
    have hj : j.1 ≤ k := Nat.le_of_lt_succ j.2
    show (j.1, k - j.1).1 + (j.1, k - j.1).2 = k
    rw [Nat.add_sub_cancel' hj]⟩
  left_inv q := by
    obtain ⟨⟨a, b⟩, hp⟩ := q
    apply Subtype.ext
    show (a, k - a) = (a, b)
    have h : k - a = b := by omega
    rw [h]
  right_inv j := by
    obtain ⟨j, hj⟩ := j
    rfl

end Entry1Corollary1BinomialSeries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
