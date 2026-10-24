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

namespace MathlibExt.Probability.DonskerWanted

/-!
# Donsker's invariance principle

This file proves the functional CLT: polygonal partial-sum processes converge in
`C([0,1],ℝ)` to Brownian motion.
-/

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

private noncomputable def donskerBrownianPath {Ω' : Type*} (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    C(Set.Icc (0 : ℝ) 1, ℝ) := by
  classical
  exact if h : Continuous (fun t : Set.Icc (0 : ℝ) 1 => B (iccToNNReal t) ω) then
    ⟨fun t => B (iccToNNReal t) ω, h⟩ else 0

private noncomputable def donskerBrownianApproximation {Ω' : Type*} (n : ℕ)
    (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') : C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ∑ k : Fin (n + 1), bernstein n k •
    ContinuousMap.const _ (B (iccToNNReal (bernstein.z k)) ω)

/-- Local Borel structures for `C(Icc 0 1, ℝ)`, scoped to avoid orphan leakage. -/
scoped instance instMeasurableSpaceContinuousMap : MeasurableSpace C(Set.Icc (0 : ℝ) 1, ℝ) :=
  borel _

scoped instance instBorelSpaceContinuousMap : BorelSpace C(Set.Icc (0 : ℝ) 1, ℝ) :=
  ⟨rfl⟩

private def bsize (a b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * b) - Nat.floor ((n : ℝ) * a)

private def bsum {Ω : Type*} (a b : ℝ) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i ∈ Finset.range (bsize a b n), X (Nat.floor ((n : ℝ) * a) + i) ω

private noncomputable def blockVec {d : ℕ} {Ω : Type*}
    (u : Fin (d + 1) → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => bsum (u j.castSucc) (u j.succ) n X ω)

private noncomputable def brownianBlockVec {d : ℕ} {Ω' : Type*}
    (u : Fin (d + 1) → ℝ≥0) (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => B (u j.succ) ω - B (u j.castSucc) ω)

private noncomputable def appendVec {d : ℕ} :
    WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → EuclideanSpace ℝ (Fin (d + 1)) :=
  fun p => WithLp.toLp 2 (Fin.lastCases p.ofLp.2 (fun i => p.ofLp.1 i))

private noncomputable def cumVec {d : ℕ} :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun v =>
  WithLp.toLp 2 (fun j =>
    ∑ k : Fin (j + 1), v ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr j.isLt)⟩)

private noncomputable def prefixVec {d : ℕ} {Ω : Type*}
    (u : Fin (d + 1) → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u j.succ : ℝ))), X i ω)

private noncomputable def brownianValueVec {d : ℕ} {Ω' : Type*}
    (u : Fin (d + 1) → ℝ≥0) (B : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => B (u j.succ) ω)

private noncomputable def interpolationCoeff (n : ℕ) (t : ℝ≥0) : ℝ :=
  if Nat.floor ((n : ℝ) * (t : ℝ)) < n then
    (Real.sqrt (n : ℝ))⁻¹ *
      ((n : ℝ) * (t : ℝ) - Nat.floor ((n : ℝ) * (t : ℝ)))
  else 0

private noncomputable def interpolationErrorVec {d : ℕ} {Ω : Type*}
    (u : Fin d → ℝ≥0) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    interpolationCoeff n (u j) * X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω)

private noncomputable def processValueVec {d : ℕ} {Ω : Type*}
    (t : Fin d → Set.Icc (0 : ℝ) 1) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => donskerProcess n X ω (t j))

private noncomputable def finsetTimes
    (I : Finset (Set.Icc (0 : ℝ) 1)) : Fin I.card → Set.Icc (0 : ℝ) 1 :=
  fun j => (I.orderIsoOfFin rfl j).1

private noncomputable def finsetTimesWithZero
    (I : Finset (Set.Icc (0 : ℝ) 1)) : Fin (I.card + 1) → ℝ≥0 :=
  Fin.cases 0 (fun j => iccToNNReal (finsetTimes I j))

private noncomputable def orderedToFinset
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    EuclideanSpace ℝ (Fin I.card) → (I → ℝ) :=
  fun z i => z ((I.orderIsoOfFin rfl).symm i)

private def psum {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, X i ω

private def level {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | a ≤ |psum X k ω|}

private def firstHit {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  disjointed (level X a) k

private def prefixTuple {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → (Finset.range k → ℝ) :=
  fun ω i => X i ω

private def tailTuple {Ω : Type*} (X : ℕ → Ω → ℝ) (k n : ℕ) :
    Ω → (Finset.Ico k n → ℝ) :=
  fun ω i => X i ω

private def tuplePsum (k : ℕ) (z : Finset.range k → ℝ) (j : Fin (k + 1)) : ℝ :=
  ∑ i : Fin j, z ⟨i, Finset.mem_range.mpr
    (lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt))⟩

private def tupleFirstHit (k : ℕ) (a : ℝ) : Set (Finset.range k → ℝ) :=
  {z | a ≤ |tuplePsum k z (Fin.last k)| ∧
    ∀ j : Fin k, |tuplePsum k z j.castSucc| < a}

private def tupleTailLarge (k n : ℕ) (a : ℝ) : Set (Finset.Ico k n → ℝ) :=
  {z | a < |∑ i, z i|}

private noncomputable def donskerGaussianFourthBound : ℝ :=
  (eLpNorm id 4 (gaussianReal 0 1)).toReal ^ 4

private def donskerGoodFamily
    (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ)) (R : ℝ) (NR : ℕ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) : Set C(Set.Icc (0 : ℝ) 1, ℝ) :=
  {f | ∃ n, f ∈ C n ∧ (NR ≤ n → ‖f‖ ≤ R) ∧
    ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j →
      dist (f s) (f t) < 1 / ((j : ℝ) + 1)}
end
