import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Ramanujan.Part1Ch5Entry5Eulerianexplicit
open scoped Nat BigOperators Polynomial
open Finset Entry4
open MathlibExt.Analysis.Ramanujan.Part1Ch5
open Entry5Eulerianexplicit


/--
[ramanujan_part1_ch5_entry5_eulerianexplicit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry5Eulerianexplicit.lean)
-/
@[path]
private lemma ramanujan_part1_ch5_entry5_eulerianexplicit_eq
  {n : ℕ}
  {p : ℂ}
-- given
  (hn : 1 ≤ n)
  (hp : p ≠ -1) :
-- imply
  p + 1 ≠ 0 ∧
    chapter5Psi 0 p = 1 ∧
    (-1 : ℂ) ^ (n + 1) * p * chapter5Psi n p / (p + 1) ^ n =
    ∑ k ∈ range (n + 1), chapter5Entry5Formula51Term n p k ∧
    chapter5Psi n p =
    ∑ j ∈ range n, chapter5Entry5Formula52Term n p j := by
-- proof
  apply MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry5Eulerianexplicit.ramanujan_part1_ch5_entry5_eulerianexplicit n p hn hp


-- created on 2026-10-20
