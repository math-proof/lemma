import Mathlib
import sympy.Basic
import sympy.atlas.Probability.BerryEsseen
open MeasureTheory ProbabilityTheory Finset Set
open scoped ProbabilityTheory ENNReal NNReal
open MathlibExt.Probability.BerryEsseenWanted


/--
[berry_esseen_finsetSum_gaussian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BerryEsseen.lean)
-/
@[path]
private lemma berry_esseen_finsetSum_gaussian_eq
  [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {ξ : ℕ → Ω → ℝ}
  {s : Finset ℕ}
  {γ z : ℝ}
-- given
  (hmeas : ∀ j, Measurable (ξ j))
  (hindep : iIndepFun ξ P)
  (hmem : ∀ j ∈ s, MemLp (ξ j) 3 P)
  (hmean : ∀ j ∈ s, P[ξ j] = 0)
  (hvar : ∑ j ∈ s, P[fun ω => (ξ j ω) ^ 2] = 1)
  (hγ : 0 ≤ γ)
  (hγ3 : ∑ j ∈ s, P[fun ω => |ξ j ω| ^ 3] ≤ γ) :
-- imply
  |P.real {ω | ∑ j ∈ s, ξ j ω ≤ z} - (gaussianReal 0 1).real (Iic z)|
    ≤ 42 * γ := by
-- proof
  apply MathlibExt.Probability.BerryEsseenWanted.berry_esseen_finsetSum_gaussian hmeas hindep hmem hmean hvar hγ hγ3 z

/--
[berry_esseen_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BerryEsseen.lean)
-/
@[path]
private lemma berry_esseen_explicit_eq
  [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → ℝ}
  {n : ℕ}
  {x : ℝ}
-- given
  (hXmeas : ∀ n, Measurable (X n))
  (hXindep : iIndepFun X P)
  (hXid : ∀ i, IdentDistrib (X i) (X 0) P P)
  (hXmem : MemLp (X 0) 3 P)
  (hXmean : P[X 0] = 0)
  (hXvar : 0 < Var[X 0; P])
  (hn : 0 < n) :
-- imply
  |((P.map (fun ω => (∑ i ∈ range n, X i ω) / Real.sqrt (n * Var[X 0; P]))).real (Iic x)
    - (gaussianReal 0 1).real (Iic x))|
    ≤ 42 * (P[fun ω => |X 0 ω| ^ 3])
    / (Real.sqrt (Var[X 0; P]) ^ 3 * Real.sqrt (n : ℝ)) := by
-- proof
  apply MathlibExt.Probability.BerryEsseenWanted.berry_esseen_explicit X hXmeas hXindep hXid hXmem hXmean hXvar n hn x

/--
[berry_esseen](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/BerryEsseen.lean)
-/
@[path]
private lemma berry_esseen_eq
  :
-- imply
  ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ),
    (∀ n, Measurable (X n)) →
    iIndepFun X P →
    (∀ i, IdentDistrib (X i) (X 0) P P) →
    Integrable (X 0) P →
    MemLp (X 0) 3 P →
    P[X 0] = 0 →
    0 < Var[X 0; P] →
    ∀ (n : ℕ), 0 < n →
    ∀ x : ℝ,
    |((P.map (fun ω => (∑ i ∈ range n, X i ω) / Real.sqrt (n * Var[X 0; P]))).real (Iic x)
    - (gaussianReal 0 1).real (Iic x))|
    ≤ C * (P[fun ω => |X 0 ω| ^ 3]) / (Real.sqrt (Var[X 0; P]) ^ 3 * Real.sqrt (n : ℝ)) := by
-- proof
  apply MathlibExt.Probability.BerryEsseenWanted.berry_esseen


-- created on 2026-10-20
