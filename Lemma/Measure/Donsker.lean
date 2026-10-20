import Mathlib
import sympy.Basic
import sympy.atlas.Probability.Donsker
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory Real
open MathlibExt.Probability.DonskerWanted


/--
[donskerProcess_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean)
-/
@[path]
private lemma donskerProcess_apply_eq_eq
  {n : ℕ}
  {X : ℕ → Ω → ℝ}
  {ω : Ω}
  {t : Set.Icc (0 : ℝ) 1}
-- given
  (hn : n ≠ 0) :
-- imply
  donskerProcess n X ω t =
    ((∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * t.1)), X i ω) +
    if Nat.floor ((n : ℝ) * t.1) < n then
    X (Nat.floor ((n : ℝ) * t.1)) ω *
    ((n : ℝ) * t.1 - Nat.floor ((n : ℝ) * t.1))
    else 0) / Real.sqrt (n : ℝ) := by
-- proof
  apply MathlibExt.Probability.DonskerWanted.donskerProcess_apply_eq n X ω t hn

/--
[continuousMap_measure_ext_of_finset_eval](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean)
-/
@[path]
private lemma continuousMap_measure_ext_of_finset_eval_eq
  {μ ν : Measure C(Set.Icc (0 : ℝ) 1, ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
-- given
  (h : ∀ I : Finset (Set.Icc (0 : ℝ) 1), μ.map (fun f => I.restrict (fun t => f t)) = ν.map (fun f => I.restrict (fun t => f t))) :
-- imply
  μ = ν := by
-- proof
  apply MathlibExt.Probability.DonskerWanted.continuousMap_measure_ext_of_finset_eval μ ν h

/--
[etemadi_maximal_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean)
-/
@[path]
private lemma etemadi_maximal_inequality_eq
  [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}
  {n : ℕ}
  {a : ℝ}
-- given
  (hX : ∀ i, Measurable (X i))
  (hIndep : iIndepFun X P) :
-- imply
  P {ω | ∃ k ∈ Finset.range (n + 1),
    3 * a ≤ |∑ i ∈ Finset.range k, X i ω|} ≤
    3 * (⨆ k ∈ Finset.range (n + 1),
    P {ω | a ≤ |∑ i ∈ Finset.range k, X i ω|}) := by
-- proof
  apply MathlibExt.Probability.DonskerWanted.etemadi_maximal_inequality X hX hIndep n a

/--
[donsker_invariance_principle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean)
-/
@[path]
private lemma donsker_invariance_principle_eq
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P']
  {X : ℕ → Ω → ℝ}
-- given
  (hMeas : ∀ n, Measurable (X n))
  (hIndep : iIndepFun X P)
  (hIdent : ∀ i, IdentDistrib (X i) (X 0) P P)
  (hInt : Integrable (X 0) P)
  (hMemLp : MemLp (X 0) 2 P)
  (hMean : P[X 0] = 0)
  (hVar : Var[X 0; P] = 1)
  (B : ℝ≥0 → Ω' → ℝ)
  (hB : IsBrownianReal B P') :
-- imply
  ∃ (Y : Ω' → C(Set.Icc (0 : ℝ) 1, ℝ)),
    (∀ᵐ ω' ∂P', ∀ t : Set.Icc (0 : ℝ) 1, (Y ω' t) = B (iccToNNReal t) ω') ∧
    TendstoInDistribution (fun n (ω : Ω) => donskerProcess n X ω) Filter.atTop Y
    (fun _ => P) P' := by
-- proof
  apply MathlibExt.Probability.DonskerWanted.donsker_invariance_principle X hMeas hIndep hIdent hInt hMemLp hMean hVar B hB


-- created on 2026-10-20
