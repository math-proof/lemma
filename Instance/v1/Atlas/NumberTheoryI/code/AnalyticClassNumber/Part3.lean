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
import Def.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part4
open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units


noncomputable section

namespace Section19

section DirichletSeries

noncomputable instance primesAbove_fintype (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) :
    Fintype {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ I} := by
  classical
  set J := Ideal.span ({(↑↑p : 𝓞 K)} : Set (𝓞 K)) with hJ_def
  have hJ_ne_bot : J ≠ ⊥ := by
    rw [hJ_def, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast p.2.ne_zero
  have h_subset : ∀ (𝔭 : Ideal (𝓞 K)),
      𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ 𝔭 →
      𝔭 ∈ (UniqueFactorizationMonoid.normalizedFactors J).toFinset := by
    intro 𝔭 ⟨h_prime, _, h_mem⟩
    rw [Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff hJ_ne_bot]
    exact ⟨h_prime, (Ideal.span_singleton_le_iff_mem 𝔭).mpr h_mem⟩
  exact Fintype.ofInjective
    (fun ⟨𝔭, h⟩ => ⟨𝔭, h_subset 𝔭 h⟩ :
      {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥ ∧ (↑↑p : 𝓞 K) ∈ I} →
      (UniqueFactorizationMonoid.normalizedFactors J).toFinset)
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp only [Subtype.mk.injEq] at h; exact Subtype.ext h)

end DirichletSeries
end Section19
end
