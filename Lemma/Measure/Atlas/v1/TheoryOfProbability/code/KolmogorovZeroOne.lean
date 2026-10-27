import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.TheoryOfProbability.code.TailSigmaAlgebra
open MeasureTheory MeasurableSpace ProbabilityTheory Filter
open scoped ENNReal MeasureTheory


/--
[tailMeasurableSpace_eq_limsup_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovZeroOne.lean)
-/
@[path]
lemma tailMeasurableSpace_eq_limsup_atTop
  {𝓐 : ℕ → MeasurableSpace Ω} :
-- imply
  tailMeasurableSpace 𝓐 = limsup 𝓐 atTop := by
-- proof
  simp only [tailMeasurableSpace, tailMeasurableSpaceFrom]
  rw [limsup_eq_iInf_iSup_of_nat]
variable {β : Type*} [mβ : MeasurableSpace β]
variable {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/--
[kolmogorov_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovZeroOne.lean)
-/
@[path]
lemma kolmogorov_zero_one
  [mβ : MeasurableSpace β]
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {𝓐 : ℕ → MeasurableSpace Ω}
  {A : Set Ω}
-- given
  (h_le : ∀ n, 𝓐 n ≤ m0)
  (h_indep : iIndep 𝓐 μ)
  (hA : MeasurableSet[tailMeasurableSpace 𝓐] A) :
-- imply
  μ A = 0 ∨ μ A = 1 := by
-- proof
  rw [tailMeasurableSpace_eq_limsup_atTop] at hA
  exact measure_zero_or_one_of_measurableSet_limsup_atTop h_le h_indep hA

/--
[kolmogorov_zero_one_fun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovZeroOne.lean)
-/
@[path]
lemma kolmogorov_zero_one_fun
  [mβ : MeasurableSpace β]
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {X : ℕ → Ω → β}
  {A : Set Ω}
-- given
  (h_le : ∀ n, MeasurableSpace.comap (X n) mβ ≤ m0)
  (h_indep : iIndep (fun n => MeasurableSpace.comap (X n) mβ) μ)
  (hA : MeasurableSet[tailMeasurableSpaceOfFun X] A) :
-- imply
  μ A = 0 ∨ μ A = 1 :=
-- proof
  kolmogorov_zero_one _ h_le h_indep hA

/--
[kolmogorov_zero_one_of_iIndepFun](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/KolmogorovZeroOne.lean)
-/
@[path]
lemma kolmogorov_zero_one_of_iIndepFun
  [mβ : MeasurableSpace β]
  {m0 : MeasurableSpace Ω}
  {μ : Measure Ω}
  {X : ℕ → Ω → β}
  {A : Set Ω}
-- given
  (h_le : ∀ n, MeasurableSpace.comap (X n) mβ ≤ m0)
  (h_indep : iIndepFun (m := fun _ => mβ) X μ)
  (hA : MeasurableSet[tailMeasurableSpaceOfFun X] A) :
-- imply
  μ A = 0 ∨ μ A = 1 :=
-- proof
  kolmogorov_zero_one_fun X h_le h_indep hA


-- created on 2026-10-23
