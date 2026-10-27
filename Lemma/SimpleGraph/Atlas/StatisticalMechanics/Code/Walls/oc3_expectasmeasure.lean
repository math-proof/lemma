import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.oc3_expectasmeasure.Part4
open Finset MeasureTheory StatMech.OSSS StatMech StatMech.Walls


/--
[oc3_siteSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_siteSum_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  ∑ b, ENNReal.ofReal (ν e b) = 1 := by
-- proof
  apply StatMech.Walls.oc3_siteSum ν hν e

/--
[oc3_siteMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_siteMeasure_singleton_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {e : E}
  {b : Bool}
-- given
  (hν : IsProbWeight ν) :
-- imply
  oc3_siteMeasure ν hν e {b} = ENNReal.ofReal (ν e b) := by
-- proof
  apply StatMech.Walls.oc3_siteMeasure_singleton ν hν e b

/--
[oc3_pwMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_pwMeasure_singleton_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ω : ConfigSpace E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  oc3_pwMeasure ν hν {ω} = ∏ e, ENNReal.ofReal (ν e (ω e)) := by
-- proof
  apply StatMech.Walls.oc3_pwMeasure_singleton ν hν ω

/--
[oc3_pwMeasure_real_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_pwMeasure_real_singleton_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {ω : ConfigSpace E}
-- given
  (hν : IsProbWeight ν) :
-- imply
  (oc3_pwMeasure ν hν).real {ω} = weight ν ω := by
-- proof
  apply StatMech.Walls.oc3_pwMeasure_real_singleton ν hν ω

/--
[oc3_expect_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_expect_eq_integral_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν g = ∫ ω, g ω ∂(oc3_pwMeasure ν hν) := by
-- proof
  apply StatMech.Walls.oc3_expect_eq_integral ν hν g

/--
[oc3_integral_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_integral_one_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  ∫ _ω, (1 : ℝ) ∂(oc3_pwMeasure ν hν) = 1 := by
-- proof
  apply StatMech.Walls.oc3_integral_one ν hν

/--
[oc3_expect_const_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_expect_const_eq_integral_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
-- given
  (hν : IsProbWeight ν) :
-- imply
  expect ν (fun _ => (1 : ℝ)) = 1 := by
-- proof
  apply StatMech.Walls.oc3_expect_const_eq_integral ν hν

/--
[oc3_bernoulliWeight_isProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_bernoulliWeight_isProb_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  IsProbWeight (oc3_bernoulliWeight (E := E) p) where nonneg := by
-- proof
  apply StatMech.Walls.oc3_bernoulliWeight_isProb hp0 hp1

/--
[oc3_expect_eq_integral_bernoulli](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_expect_eq_integral_bernoulli_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  expect (oc3_bernoulliWeight (E := E) p) g = ∫ ω, g ω ∂(oc3_pwMeasure (oc3_bernoulliWeight (E := E) p) (oc3_bernoulliWeight_isProb hp0 hp1)) := by
-- proof
  apply StatMech.Walls.oc3_expect_eq_integral_bernoulli hp0 hp1 g

/--
[oc3_fk_expect_eq_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_fk_expect_eq_integral_eq
  [Fintype E]
  [DecidableEq E]
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
  {g : ConfigSpace (Sym2 V) → ℝ}
-- given
  (hp0 : 0 ≤ p)
  (hp1 : p ≤ 1) :
-- imply
  expect (oc3_bernoulliWeight (E := Sym2 V) p) g = ∫ ω, g ω ∂(oc3_pwMeasure (oc3_bernoulliWeight (E := Sym2 V) p) (oc3_bernoulliWeight_isProb hp0 hp1)) := by
-- proof
  apply StatMech.Walls.oc3_fk_expect_eq_integral hp0 hp1 g

/--
[oc3_vcubeProb_dep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc3_expectasmeasure.lean)
-/
@[path]
private lemma oc3_vcubeProb_dep_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  IsProbabilityMeasure (StatMech.OSSS.GrandCoupling.Vcube n) := by
-- proof
  apply StatMech.Walls.oc3_vcubeProb_dep n


-- created on 2026-10-23
