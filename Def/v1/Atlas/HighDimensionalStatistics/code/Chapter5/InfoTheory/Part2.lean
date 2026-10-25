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
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Lemma_5_14.Part5
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Lemma_5_14
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter1.Thm_1_9
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Convex.Jensen
import Theorem.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory
open MeasureTheory InformationTheory Real


noncomputable section

namespace InfoTheory

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

end InfoTheory
end
