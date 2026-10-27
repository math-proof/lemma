import Mathlib.Analysis.SpecificLimits.Basic
import Def.Analysis.Real.Limits.Part4
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic
open Topology


@[path]
private lemma main
  {x : ℝ}
-- given
  (h : x ∈ Ioo (-1 : ℝ) 0) :
-- imply
  lim [n → ∞] x ^ n = 0 := by
-- proof
  obtain ⟨h1, h2⟩ := h
  have h' : |x| < 1 := by
    rw [abs_of_neg h2]
    linarith
  exact tendsto_pow_atTop_nhds_zero_iff.mpr h'


-- created on 2023-04-17
