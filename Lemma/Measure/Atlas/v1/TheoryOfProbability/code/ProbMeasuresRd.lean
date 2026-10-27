import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfProbability.code.ProbMeasuresRd
open MeasureTheory MeasurableSpace Set


namespace MeasureTheory

/--
[Real.isCountablySpanning_range_Iic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma Real.isCountablySpanning_range_Iic
-- imply
  IsCountablySpanning (range (Iic : ℝ → Set ℝ)) :=
-- proof
  ⟨fun n => Iic (n : ℝ), fun n => mem_range.mpr ⟨n, rfl⟩, by
    ext x; simp only [Set.mem_iUnion, Set.mem_Iic, Set.mem_univ, iff_true]
    exact ⟨⌈x⌉₊, Nat.le_ceil x⟩⟩

end MeasureTheory

namespace MeasureTheory

/--
[Real.generateFrom_range_Iic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma Real.generateFrom_range_Iic
-- imply
  generateFrom (range (Iic : ℝ → Set ℝ)) = (inferInstance : MeasurableSpace ℝ) :=
-- proof
  (borel_eq_generateFrom_Iic ℝ).symm.trans BorelSpace.measurable_eq.symm

end MeasureTheory

namespace MeasureTheory

/--
[isPiSystem_piIic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma isPiSystem_piIic
  {d : ℕ} :
-- imply
  IsPiSystem (univ.pi '' univ.pi (fun _ : Fin d => range (Iic : ℝ → Set ℝ))) :=
-- proof
  IsPiSystem.pi fun _ => isPiSystem_Iic

end MeasureTheory

namespace MeasureTheory

/--
[generateFrom_piIic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma generateFrom_piIic
  {d : ℕ} :
-- imply
  generateFrom (univ.pi '' univ.pi (fun _ : Fin d => range (Iic : ℝ → Set ℝ))) = (inferInstance : MeasurableSpace (Fin d → ℝ)) :=
-- proof
  generateFrom_eq_pi
    (fun _ => Real.generateFrom_range_Iic)
    (fun _ => Real.isCountablySpanning_range_Iic)

end MeasureTheory

namespace MeasureTheory

/--
[ProbabilityMeasure.ext_of_Iic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma ProbabilityMeasure.ext_of_Iic
  {d : ℕ}
  {μ ν : Measure (Fin d → ℝ)}
  [IsProbabilityMeasure μ]
  [IsProbabilityMeasure ν]
-- given
  (h : ∀ a : Fin d → ℝ, μ (Iic a) = ν (Iic a)) :
-- imply
  μ = ν := by
-- proof
  apply ext_of_generate_finite
    (univ.pi '' univ.pi (fun _ : Fin d => range (Iic : ℝ → Set ℝ)))
  ·
    exact (generateFrom_piIic d).symm
  ·
    exact isPiSystem_piIic d
  ·
    intro s hs
    obtain ⟨f, hf, rfl⟩ := hs
    choose a ha using fun i => hf i (Set.mem_univ i)
    have : univ.pi f = Iic a := by
      ext x; simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Pi.le_def]
      exact forall_congr' fun i => by rw [← ha i]; simp [Set.mem_Iic]
    rw [this]; exact h a
  ·
    simp [measure_univ]

end MeasureTheory

/--
[isPiSystem_C_Ioc_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma isPiSystem_C_Ioc_pi
-- imply
  IsPiSystem C_Ioc_pi := by
-- proof
  have := isPiSystem_Ioc_mem (univ : Set ℝ) univ
  simp only [mem_univ, true_and] at this; exact this

/--
[generateFrom_C_Ioc_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma generateFrom_C_Ioc_pi
-- imply
  generateFrom C_Ioc_pi = (inferInstance : MeasurableSpace ℝ) := by
-- proof
  rw [show (inferInstance : MeasurableSpace ℝ) = borel ℝ from BorelSpace.measurable_eq]
  exact (borel_eq_generateFrom_Ioc ℝ).symm

/--
[isCountablySpanning_C_Ioc_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/ProbMeasuresRd.lean)
-/
@[path]
lemma isCountablySpanning_C_Ioc_pi
-- imply
  IsCountablySpanning C_Ioc_pi := by
-- proof
  refine ⟨fun n => Ioc (-(n : ℝ) - 1) (n + 1), ?_, ?_⟩
  · intro n; exact ⟨-(n : ℝ) - 1, n + 1, by linarith, rfl⟩
  · ext x; simp only [mem_iUnion, mem_Ioc, mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (|x|)
    exact ⟨n, by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
/-- **Characterization of probability measures on `ℝᵈ`**. Given `F : ℝᵈ → ℝ` that is
coordinate-wise non-decreasing, coordinate-wise right-continuous, and rectangle-nonnegative,
there exists a *unique* Borel measure `μ` on `ℝᵈ` whose value on each finite rectangle
`(a, b]` is determined by the inclusion–exclusion `rectangleValue F a b`. -/


-- created on 2026-10-23
