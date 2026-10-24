/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/InfoTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.InformationTheory.KullbackLeibler.KLFun
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.L2Space
import sympy.atlas.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen

open MeasureTheory InformationTheory Real

noncomputable section

namespace InfoTheory

/-- Total variation distance between probability measures `P₀` and `P₁` on a measurable space,
defined as the supremum of `|P₀ S - P₁ S|` over measurable sets `S`. (Definition 5.4.) -/
noncomputable def tvDist {Ω : Type*} [MeasurableSpace Ω]
    (P₀ P₁ : Measure Ω) : ℝ :=
  sSup {x : ℝ | ∃ S : Set Ω, MeasurableSet S ∧ x = |(P₀ S).toReal - (P₁ S).toReal|}

/-- Real-valued version of the Kullback–Leibler divergence `klDiv P Q`, obtained by
taking `toReal` of the `ℝ≥0∞`-valued divergence. -/
noncomputable def klDiv_real {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  (klDiv P Q).toReal

/-- Bhattacharyya coefficient `BC(P, Q) = ∫ √(dP/dQ) dQ` between two measures. -/
noncomputable def bhattacharyyaCoeff {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) : ℝ :=
  ∫ ω, Real.sqrt (P.rnDeriv Q ω).toReal ∂Q

/-- Uniform mixture measure `(1/M) ∑ⱼ Pⱼ` of a finite family of probability measures. -/
noncomputable def mixtureMeasure {Ω : Type*} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin M → Measure Ω) : Measure Ω :=
  (1 / (M : ENNReal)) • Finset.sum Finset.univ (fun j => P j)

/-- Squared Euclidean distance between two vectors `θ₁, θ₂ ∈ ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- `isMinIdx f n` holds when `n < M` and `f ⟨n, _⟩` is a minimum of `f` over `Fin M`. -/
def isMinIdx {M : ℕ} (f : Fin M → ℝ) (n : ℕ) : Prop :=
  ∃ h : n < M, ∀ k : Fin M, f ⟨n, h⟩ ≤ f k

/-- Decidability instance for `isMinIdx`, obtained classically. -/
instance isMinIdx.decidable {M : ℕ} (f : Fin M → ℝ) : DecidablePred (isMinIdx f) :=
  fun _ => Classical.dec _

/-- A nonempty finite real-valued function has at least one minimising index. -/
lemma exists_isMinIdx {M : ℕ} (f : Fin M → ℝ) (hM : 0 < M) : ∃ n, isMinIdx f n := by
  obtain ⟨j, _, hj⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin M)) f
    ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  exact ⟨j.val, j.isLt, fun k => hj k (Finset.mem_univ _)⟩

/-- Deterministic nearest-neighbour argmin operator: returns the smallest minimising index
of `f : Fin M → ℝ` (with `M > 0`). -/
def nnArgmin {M : ℕ} (f : Fin M → ℝ) (hM : 0 < M) : Fin M :=
  ⟨Nat.find (exists_isMinIdx f hM), (Nat.find_spec (exists_isMinIdx f hM)).choose⟩

/-- Hamming distance between two Boolean vectors: the number of coordinates where they differ. -/
def hammingDist {d : ℕ} (ω₁ ω₂ : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω₁ i ≠ ω₂ i).card

/-- Equivalence between the subtype `{i ∈ {j, k}}` and `Fin 2`, sending `j` to `0` and `k`
to `1`, for distinct indices `j ≠ k`. -/
noncomputable def pairSubtypeEquivFin2 {M : ℕ} (j k : Fin M) (hjk : j ≠ k) :
    {i : Fin M // i ∈ ({j, k} : Finset (Fin M))} ≃ Fin 2 where
  toFun := fun ⟨i, hi⟩ => if i = j then 0 else 1
  invFun := fun n => if h : n = 0 then ⟨j, Finset.mem_insert.mpr (Or.inl rfl)⟩
    else ⟨k, Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))⟩
  left_inv := by
    intro ⟨i, hi⟩; simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    cases hi with
    | inl h => subst h; simp
    | inr h => subst h; simp [hjk.symm, show (1 : Fin 2) ≠ 0 from by decide]
  right_inv := by
    intro n; fin_cases n
    · simp
    · simp only [show (⟨1, by omega⟩ : Fin 2) ≠ 0 from by decide, dite_false]; simp [hjk.symm]

/-- For distinct indices `j ≠ k`, the space of functions `Fin M → α` is equivalent to the
product of `α × α` (the values at `j` and `k`) and the functions on the complementary indices. -/
noncomputable def fiberEquiv {M : ℕ} (j k : Fin M) (hjk : j ≠ k) (α : Type*) :
    (Fin M → α) ≃ (α × α) × ({i : Fin M // i ∉ ({j, k} : Finset (Fin M))} → α) :=
  (Equiv.piEquivPiSubtypeProd (· ∈ ({j, k} : Finset (Fin M))) (fun _ => α)).trans
    (Equiv.prodCongrLeft fun _ =>
      ((Equiv.piCongrLeft' (fun _ => α) (pairSubtypeEquivFin2 j k hjk)).trans
        (finTwoArrowEquiv α)))

open ProbabilityTheory in
/-- The uniform probability measure on `Bool`. -/
noncomputable def μ_Bool : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure

/-- The uniform Boolean measure `μ_Bool` is a probability measure. -/
instance μ_Bool_prob : IsProbabilityMeasure μ_Bool :=
  PMF.toMeasure.isProbabilityMeasure _

/-- Centering map sending `true ↦ 1/2` and `false ↦ -1/2`, used to turn Boolean variables
into centered `±1/2`-valued random variables. -/
noncomputable def boolCenter (b : Bool) : ℝ := if b then (1 : ℝ) / 2 else -(1 : ℝ) / 2

/-- The "XOR pairing" self-equivalence on `(Fin d → Bool) × (Fin d → Bool)`, sending
`(a, b)` to `(a, a ^^ b)`. Used to reduce pair-counting arguments to single-string counts. -/
def pairXorEquiv (d : ℕ) :
    (Fin d → Bool) × (Fin d → Bool) ≃ (Fin d → Bool) × (Fin d → Bool) where
  toFun p := (p.1, fun i => p.1 i ^^ p.2 i)
  invFun q := (q.1, fun i => q.1 i ^^ q.2 i)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- The `ℓ⁰`-norm of a Boolean vector: the number of coordinates equal to `true`. -/
def l0norm_bool {d : ℕ} (ω : Fin d → Bool) : ℕ :=
  (Finset.univ.filter fun i => ω i = true).card
