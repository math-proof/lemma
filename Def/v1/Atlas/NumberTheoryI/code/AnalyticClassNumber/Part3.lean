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
import Abbrev.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part2
open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units


noncomputable section

namespace Section19

section DirichletSeries

set_option backward.isDefEq.respectTransparency false in

def characterAnnihilator (m : ℕ) (H : Subgroup (DirichletCharacter ℂ m)) :
    Subgroup (ZMod m)ˣ where
  carrier := {u | ∀ χ ∈ H, χ u.val = 1}
  mul_mem' {a b} ha hb χ hχ := by rw [Units.val_mul, map_mul, ha χ hχ, hb χ hχ, one_mul]
  one_mem' χ _ := by rw [Units.val_one, map_one]
  inv_mem' {a} ha χ hχ := by
    have h1 := ha χ hχ
    have h2 : χ a.val * χ a⁻¹.val = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rw [h1, one_mul] at h2; exact h2

def galoisAnnihilator (m : ℕ) [NeZero m] (H : Subgroup (DirichletCharacter ℂ m)) :
    Subgroup ((CyclotomicField m ℚ) ≃ₐ[ℚ] (CyclotomicField m ℚ)) :=
  (characterAnnihilator m H).comap
    (IsCyclotomicExtension.Rat.galEquivZMod m (CyclotomicField m ℚ)).toMonoidHom

def fixedFieldOfCharacterSubgroup (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) :
    IntermediateField ℚ (CyclotomicField m ℚ) :=
  IntermediateField.fixedField (galoisAnnihilator m H)

end DirichletSeries
end Section19
end
