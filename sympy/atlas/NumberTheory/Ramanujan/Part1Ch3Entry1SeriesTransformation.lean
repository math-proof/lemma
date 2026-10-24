/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry1SeriesTransformation.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 1

Series transformation relates Q-weighted Taylor coefficients at 0, 1.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry1SeriesTransformation

private def fibEquiv (n : ℕ) : Fin (n + 1) ≃ {p : ℕ × ℕ // p.1 + p.2 = n} where
  toFun j := ⟨(j.val, n - j.val), by have hj := j.2; show j.val + (n - j.val) = n; omega⟩
  invFun q := ⟨q.val.1, by have hq := q.property; omega⟩
  left_inv j := by
    obtain ⟨jv, hj⟩ := j
    rfl
  right_inv q := by
    obtain ⟨⟨j, k⟩, hk⟩ := q
    have hk' : j + k = n := hk
    apply Subtype.ext
    show (j, n - j) = (j, k)
    rw [Prod.mk.injEq]
    exact ⟨rfl, by omega⟩
end Entry1SeriesTransformation
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
