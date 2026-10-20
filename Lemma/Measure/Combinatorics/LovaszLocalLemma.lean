import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Combinatorics.LovaszLocalLemma
open Finset SimpleGraph
open scoped BigOperators
open MathlibExt.Probability.Combinatorics.LovaszLocalLemma


/--
[lovasz_local_lemma_symmetric_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Combinatorics/LovaszLocalLemma.lean)
-/
@[path]
private lemma lovasz_local_lemma_symmetric_finite_eq
  [Fintype Ω] [Fintype I] [DecidableEq I]
  {pmf : Ω → ℝ}
  {A : I → Set Ω}
  {G : SimpleGraph I} [DecidableRel G.Adj]
  {p : ℝ}
  {d : ℕ}
-- given
  (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
  (hpmf_sum : ∑ ω : Ω, pmf ω = 1)
  (hp_nonneg : 0 ≤ p)
  (hmaxDeg : G.maxDegree ≤ d)
  (hp_le : ∀ i : I, ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤ p)
  (hDep : ∀ (i : I) (S : Finset I), (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) → ∑ ω : Ω, (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) = (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) * (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
  (hExp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
-- imply
  0 < ∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0) := by
-- proof
  apply MathlibExt.Probability.Combinatorics.LovaszLocalLemma.lovasz_local_lemma_symmetric_finite pmf hpmf_nonneg hpmf_sum A G p d hp_nonneg hmaxDeg hp_le hDep hExp


-- created on 2026-10-20
