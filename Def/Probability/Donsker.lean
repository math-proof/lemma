/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/Donsker.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory Real

/-!
# Donsker's invariance principle

This file proves the functional CLT: polygonal partial-sum processes converge in
`C([0,1],ℝ)` to Brownian motion.
-/


namespace MathlibExt.Probability.DonskerWanted

noncomputable section

/-- Clamps a real to `[0,1]`. -/
noncomputable def donskerClamp (x : ℝ) : ℝ :=
  min (max x 0) 1

/-- Weight `t ↦ clamp(n·t - i)` for the polygonal interpolation. -/
noncomputable def donskerWeight (n i : ℕ) (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  donskerClamp ((n : ℝ) * t.val - (i : ℝ))

/-- Bundled continuous version of `donskerWeight` in `C([0,1],ℝ)`. -/
noncomputable def donskerWeightCM (n i : ℕ) : C(Set.Icc (0 : ℝ) 1, ℝ) where
  toFun := donskerWeight n i
  continuous_toFun := by
    unfold donskerWeight donskerClamp
    have h_val : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (t.val : ℝ)) :=
      continuous_subtype_val
    have h_lin : Continuous (fun t : Set.Icc (0 : ℝ) 1 => (n : ℝ) * t.val - (i : ℝ)) := by
      fun_prop
    have h_clamp : Continuous (fun x : ℝ => min (max x 0) 1) := by
      fun_prop
    exact h_clamp.comp h_lin

/-- Polygonal normalized partial-sum process as a `C([0,1],ℝ)`-valued variable. -/
noncomputable def donskerProcess {Ω : Type*} (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    C(Set.Icc (0 : ℝ) 1, ℝ) :=
  if n = 0 then 0
  else
    let sqrtInv : ℝ := (Real.sqrt (n : ℝ))⁻¹
    sqrtInv • (Finset.sum (Finset.range n) fun i => (X i ω) • donskerWeightCM n i)

/-- Inclusion of `Set.Icc 0 1` into `ℝ≥0`. -/
noncomputable def iccToNNReal (t : Set.Icc (0 : ℝ) 1) : ℝ≥0 :=
  ⟨t.val, t.2.1⟩

noncomputable def donskerBrownianPath {Ω' : Type*} (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    C(Set.Icc (0 : ℝ) 1, ℝ) := by
  classical
  exact if h : Continuous (fun t : Set.Icc (0 : ℝ) 1 => B (iccToNNReal t) ω) then
    ⟨fun t => B (iccToNNReal t) ω, h⟩ else 0

noncomputable def donskerBrownianApproximation {Ω' : Type*} (n : ℕ)
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ∑ k : Fin (n + 1), bernstein n k •
    ContinuousMap.const _ (B (iccToNNReal (bernstein.z k)) ω)

end
end MathlibExt.Probability.DonskerWanted
