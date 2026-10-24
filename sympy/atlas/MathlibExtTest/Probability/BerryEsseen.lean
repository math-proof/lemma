/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/BerryEsseen.lean -/


import sympy.atlas.Probability.BerryEsseen
import Lemma.Measure.BerryEsseen


open MeasureTheory ProbabilityTheory Finset Set
open scoped ProbabilityTheory ENNReal NNReal

open MathlibExt.Probability.BerryEsseenWanted

/-- The finite-sum public API exposes the exact `gaussianReal` signature. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hmeas : ∀ j, Measurable (ξ j))
    (hindep : iIndepFun ξ P) {s : Finset ℕ}
    (hmem : ∀ j ∈ s, MemLp (ξ j) 3 P)
    (hmean : ∀ j ∈ s, P[ξ j] = 0)
    (hvar : ∑ j ∈ s, P[fun ω => (ξ j ω) ^ 2] = 1)
    {γ : ℝ} (hγ : 0 ≤ γ)
    (hγ3 : ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] ≤ γ)
    (z : ℝ) :
    |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - (gaussianReal 0 1).real (Iic z)|
      ≤ 42 * γ :=
  berry_esseen_finsetSum_gaussian hmeas hindep hmem hmean hvar hγ hγ3 z

/-- The i.i.d. public API exposes the explicit constant `42`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hXmeas : ∀ n, Measurable (X n))
    (hXindep : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXmem : MemLp (X 0) 3 P)
    (hXmean : P[X 0] = 0)
    (hXvar : 0 < Var[X 0; P])
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    |((P.map (fun ω => (∑ i ∈ range n, X i ω) / Real.sqrt (n * Var[X 0; P]))).real (Iic x)
      - (gaussianReal 0 1).real (Iic x))|
      ≤ 42 * (P[fun ω => |X 0 ω| ^ 3])
        / (Real.sqrt (Var[X 0; P]) ^ 3 * Real.sqrt (n : ℝ)) :=
  berry_esseen_explicit X hXmeas hXindep hXid hXmem hXmean hXvar n hn x

/-- A client can apply the existential bound at a concrete model. -/
example {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hXmeas : ∀ n, Measurable (X n))
    (hXindep : iIndepFun X P)
    (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hXint : Integrable (X 0) P)
    (hXmem : MemLp (X 0) 3 P)
    (hXmean : P[X 0] = 0)
    (hXvar : 0 < Var[X 0; P])
    (n : ℕ) (hn : 0 < n) (x : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      |((P.map (fun ω => (∑ i ∈ range n, X i ω) / Real.sqrt (n * Var[X 0; P]))).real (Iic x)
        - (gaussianReal 0 1).real (Iic x))|
      ≤ C * (P[fun ω => |X 0 ω| ^ 3])
        / (Real.sqrt (Var[X 0; P]) ^ 3 * Real.sqrt (n : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := berry_esseen
  exact ⟨C, hCpos, hC X hXmeas hXindep hXid hXint hXmem hXmean hXvar n hn x⟩
