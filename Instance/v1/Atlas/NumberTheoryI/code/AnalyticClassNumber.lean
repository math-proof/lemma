/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.Deriv
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Order.ModularLattice
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Theorem.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber

@[expose] public section

open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units


noncomputable section

namespace Section19

section DirichletSeries

instance pFreePart_neZero {m : ℕ} [NeZero m] (p : ℕ) : NeZero (pFreePart m p) :=
  ⟨(pFreePart_pos (NeZero.pos m) p).ne'⟩

noncomputable instance cyclotomicSubgroupModular (m : ℕ) [NeZero m] :
    IsModularLattice (Subgroup (CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ)) := by
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  have hm : 0 < m := NeZero.pos m
  have hirr := Polynomial.cyclotomic.irreducible_rat hm
  have oi := (IsCyclotomicExtension.autEquivPow (CyclotomicField m ℚ) hirr).mapSubgroup
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (oi y) (oi.le_iff_le.mpr hxz)
  rw [← oi.map_sup, ← oi.map_inf, ← oi.map_inf, ← oi.map_sup] at h
  exact oi.le_iff_le.mp h

noncomputable instance cyclotomicIntermediateFieldModular (m : ℕ) [NeZero m] :
    IsModularLattice (IntermediateField ℚ (CyclotomicField m ℚ)) := by
  haveI : IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
    CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero m ℚ
  haveI : IsGalois ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.isGalois {m} ℚ (CyclotomicField m ℚ)
  have e := IsGalois.intermediateFieldEquivSubgroup (F := ℚ) (E := CyclotomicField m ℚ)
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (e y) (e.le_iff_le.mpr hxz)
  rw [← e.map_sup, ← e.map_inf, ← e.map_inf, ← e.map_sup] at h
  exact e.le_iff_le.mp h

instance instNeZeroCastRat (m : ℕ) [NeZero m] : NeZero (m : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (NeZero.ne m)⟩

instance instIsCyclotomicExtensionCyclotomicField (m : ℕ) [NeZero m] :
    IsCyclotomicExtension {m} ℚ (CyclotomicField m ℚ) :=
  CyclotomicField.isCyclotomicExtension m ℚ

end DirichletSeries
end Section19
end
