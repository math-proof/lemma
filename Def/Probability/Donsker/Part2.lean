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
import Instance.Probability.Donsker
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory Real

/-!
# Donsker's invariance principle

This file proves the functional CLT: polygonal partial-sum processes converge in
`C([0,1],ℝ)` to Brownian motion.
-/


namespace MathlibExt.Probability.DonskerWanted

noncomputable section

def bsize (a b : ℝ) (n : ℕ) : ℕ :=
  Nat.floor ((n : ℝ) * b) - Nat.floor ((n : ℝ) * a)

def bsum {Ω : Type*} (a b : ℝ) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹ *
    ∑ i ∈ Finset.range (bsize a b n), X (Nat.floor ((n : ℝ) * a) + i) ω

noncomputable def blockVec {d : ℕ} {Ω : Type*}
    (u : Fin (d + 1) → NNReal) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => bsum (u j.castSucc) (u j.succ) n X ω)

noncomputable def brownianBlockVec {d : ℕ} {Ω' : Type*}
    (u : Fin (d + 1) → NNReal) (B : NNReal → Ω' → ℝ) (ω : Ω') :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => B (u j.succ) ω - B (u j.castSucc) ω)

noncomputable def appendVec {d : ℕ} :
    WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → EuclideanSpace ℝ (Fin (d + 1)) :=
  fun p => WithLp.toLp 2 (Fin.lastCases p.ofLp.2 (fun i => p.ofLp.1 i))

noncomputable def cumVec {d : ℕ} :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) := fun v =>
  WithLp.toLp 2 (fun j =>
    ∑ k : Fin (j + 1), v ⟨k, lt_of_lt_of_le k.isLt (Nat.succ_le_iff.mpr j.isLt)⟩)

noncomputable def prefixVec {d : ℕ} {Ω : Type*}
    (u : Fin (d + 1) → NNReal) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    (Real.sqrt (n : ℝ))⁻¹ *
      ∑ i ∈ Finset.range (Nat.floor ((n : ℝ) * (u j.succ : ℝ))), X i ω)

noncomputable def brownianValueVec {d : ℕ} {Ω' : Type*}
    (u : Fin (d + 1) → NNReal) (B : NNReal → Ω' → ℝ) (ω : Ω') :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => B (u j.succ) ω)

noncomputable def interpolationCoeff (n : ℕ) (t : NNReal) : ℝ :=
  if Nat.floor ((n : ℝ) * (t : ℝ)) < n then
    (Real.sqrt (n : ℝ))⁻¹ *
      ((n : ℝ) * (t : ℝ) - Nat.floor ((n : ℝ) * (t : ℝ)))
  else 0

noncomputable def interpolationErrorVec {d : ℕ} {Ω : Type*}
    (u : Fin d → NNReal) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j =>
    interpolationCoeff n (u j) * X (Nat.floor ((n : ℝ) * (u j : ℝ))) ω)

noncomputable def processValueVec {d : ℕ} {Ω : Type*}
    (t : Fin d → Set.Icc (0 : ℝ) 1) (n : ℕ) (X : ℕ → Ω → ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => donskerProcess n X ω (t j))

noncomputable def finsetTimes
    (I : Finset (Set.Icc (0 : ℝ) 1)) : Fin I.card → Set.Icc (0 : ℝ) 1 :=
  fun j => (I.orderIsoOfFin rfl j).1

noncomputable def finsetTimesWithZero
    (I : Finset (Set.Icc (0 : ℝ) 1)) : Fin (I.card + 1) → NNReal :=
  Fin.cases 0 (fun j => iccToNNReal (finsetTimes I j))

noncomputable def orderedToFinset
    (I : Finset (Set.Icc (0 : ℝ) 1)) :
    EuclideanSpace ℝ (Fin I.card) → (I → ℝ) :=
  fun z i => z ((I.orderIsoOfFin rfl).symm i)

def psum {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, X i ω

def level {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  {ω | a ≤ |psum X k ω|}

def firstHit {Ω : Type*} (X : ℕ → Ω → ℝ) (a : ℝ) (k : ℕ) : Set Ω :=
  disjointed (level X a) k

def prefixTuple {Ω : Type*} (X : ℕ → Ω → ℝ) (k : ℕ) :
    Ω → (Finset.range k → ℝ) :=
  fun ω i => X i ω

def tailTuple {Ω : Type*} (X : ℕ → Ω → ℝ) (k n : ℕ) :
    Ω → (Finset.Ico k n → ℝ) :=
  fun ω i => X i ω

def tuplePsum (k : ℕ) (z : Finset.range k → ℝ) (j : Fin (k + 1)) : ℝ :=
  ∑ i : Fin j, z ⟨i, Finset.mem_range.mpr
    (lt_of_lt_of_le i.isLt (Nat.le_of_lt_succ j.isLt))⟩

def tupleFirstHit (k : ℕ) (a : ℝ) : Set (Finset.range k → ℝ) :=
  {z | a ≤ |tuplePsum k z (Fin.last k)| ∧
    ∀ j : Fin k, |tuplePsum k z j.castSucc| < a}

def tupleTailLarge (k n : ℕ) (a : ℝ) : Set (Finset.Ico k n → ℝ) :=
  {z | a < |∑ i, z i|}

noncomputable def donskerGaussianFourthBound : ℝ :=
  (eLpNorm id 4 (gaussianReal 0 1)).toReal ^ 4

def donskerGoodFamily
    (C : ℕ → Set C(Set.Icc (0 : ℝ) 1, ℝ)) (R : ℝ) (NR : ℕ)
    (δ : ℕ → ℝ) (N : ℕ → ℕ) : Set C(Set.Icc (0 : ℝ) 1, ℝ) :=
  {f | ∃ n, f ∈ C n ∧ (NR ≤ n → ‖f‖ ≤ R) ∧
    ∀ j, N j ≤ n → ∀ s t : Set.Icc (0 : ℝ) 1, dist s t ≤ δ j →
      dist (f s) (f t) < 1 / ((j : ℝ) + 1)}

end
end MathlibExt.Probability.DonskerWanted
