/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/Combinatorics/LovaszLocalLemma.lean -/


import sympy.atlas.Probability.Combinatorics.LovaszLocalLemma
import Lemma.Measure.Combinatorics.LovaszLocalLemma


open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- The public theorem exposes the exact Wanted signature. -/
example {Ω : Type*} {I : Type*} [Fintype Ω] [DecidableEq Ω]
    [Fintype I] [DecidableEq I]
    (pmf : Ω → ℝ)
    (hpmf_nonneg : ∀ ω, 0 ≤ pmf ω)
    (hpmf_sum : ∑ ω : Ω, pmf ω = 1)
    (A : I → Set Ω)
    (G : SimpleGraph I) [DecidableRel G.Adj]
    (p : ℝ) (d : ℕ)
    (hp_nonneg : 0 ≤ p)
    (hmaxDeg : G.maxDegree ≤ d)
    (hp_le : ∀ i : I,
      ∑ ω : Ω, (if ω ∈ A i then pmf ω else 0) ≤ p)
    (hDep : ∀ (i : I) (S : Finset I),
      (∀ j ∈ S, j ∉ insert i (G.neighborSet i)) →
      ∑ ω : Ω,
        (if ω ∈ A i ∧ ∀ j ∈ S, ω ∈ A j then pmf ω else 0) =
      (∑ ω : Ω, (if ω ∈ A i then pmf ω else 0)) *
      (∑ ω : Ω, (if ∀ j ∈ S, ω ∈ A j then pmf ω else 0)))
    (hExp : Real.exp 1 * p * ((d : ℝ) + 1) ≤ 1) :
    0 < ∑ ω : Ω, (if ∀ i : I, ω ∉ A i then pmf ω else 0) :=
  MathlibExt.Probability.Combinatorics.LovaszLocalLemma.lovasz_local_lemma_symmetric_finite
    pmf hpmf_nonneg hpmf_sum A G p d hp_nonneg hmaxDeg hp_le hDep hExp

/-- Edge case: with an empty family of bad events on a one-point space,
avoidance has full probability. -/
example : 0 < ∑ ω : Fin 1, (if ∀ _i : Empty, ω ∉ (∅ : Set (Fin 1)) then (1 : ℝ) else
    0) := by
  classical
  refine MathlibExt.Probability.Combinatorics.LovaszLocalLemma.lovasz_local_lemma_symmetric_finite
    (Ω := Fin 1) (I := Empty)
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (by simp) (fun _ => (∅ : Set (Fin 1)))
    (⊥ : SimpleGraph Empty) 0 (SimpleGraph.maxDegree ⊥) le_rfl le_rfl
    (fun i => i.elim) (fun i => i.elim) (by simp)
