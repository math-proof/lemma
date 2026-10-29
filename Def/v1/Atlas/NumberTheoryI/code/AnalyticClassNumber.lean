/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Order.ModularLattice
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.RingTheory.Ideal.NatInt
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units


noncomputable section

namespace Section19

section LipschitzParametrizable

def IsLipschitzContinuous {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (f : X → Y) : Prop :=
  ∃ K : NNReal, LipschitzWith K f

def IsLipschitzParametrizable {X : Type*} [PseudoMetricSpace X] (B : Set X) (d : ℕ) : Prop :=
  ∃ (m : ℕ) (f : Fin m → ((Fin d → ℝ) → X)),
    (∀ i, ∃ K : NNReal, LipschitzWith K (f i)) ∧
    B ⊆ ⋃ i, (f i) '' (Set.pi Set.univ (fun _ => Set.Icc 0 1))

def outerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {v | ∃ x : Fin n → ℝ, (∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1) ∧
    (fun i => x i / t) ∈ S}

def innerCubeSet {n : ℕ} (S : Set (Fin n → ℝ)) (t : ℝ) : Set (Fin n → ℤ) :=
  {v | ∀ x : Fin n → ℝ, (∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1) →
    (fun i => x i / t) ∈ S}

noncomputable def unitCube {n : ℕ} (v : Fin n → ℤ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun i => Set.Ico (v i : ℝ) ((v i : ℝ) + 1))

noncomputable def idealToClass (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : ClassGroup (𝓞 K) :=
  ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩

noncomputable def toFinME : (NumberField.mixedEmbedding.euclidean.mixedSpace K) ≃ᵐ
    (Fin (Module.finrank ℚ K) → ℝ) := by
  classical
  have hcard : Fintype.card (NumberField.mixedEmbedding.index K) = Module.finrank ℚ K := by
    linarith [NumberField.mixedEmbedding.euclidean.finrank K,
      Module.finrank_eq_card_basis
        (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).toBasis]
  let onb := (NumberField.mixedEmbedding.euclidean.stdOrthonormalBasis K).reindex
    (Fintype.equivFinOfCardEq hcard)
  exact onb.measurableEquiv.trans
    (MeasurableEquiv.toLp 2 (Fin (Module.finrank ℚ K) → ℝ)).symm

end AnalyticClassNumber

section DirichletSeries

noncomputable def dirichletSeriesAbel (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * ∫ x in Set.Ioi (1 : ℝ), (∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1)) *
    (x : ℂ) ^ (-(s + 1))

noncomputable def dirichletSeriesContinuation (a : ℕ → ℂ) (ρ : ℂ) : ℂ → ℂ :=
  fun s => ρ * riemannZeta s + dirichletSeriesAbel (fun n => a n - ρ) s

open Finset in

set_option maxHeartbeats 400000 in

def stepFnAbel (f : ℕ → ℂ) (x : ℝ) : ℂ :=
  if x > 1 then ∑ n ∈ Finset.range ⌊x⌋₊, f (n + 1) else 0

def IsUnramifiedAtPrime (K : Type*) [Field K] [NumberField K] (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 K)) [P.IsPrime],
    P.LiesOver (Ideal.span {(p : ℤ)}) →
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1

def pFreePart (m p : ℕ) : ℕ := m / p ^ padicValNat p m

end DirichletSeries
end Section19
end
