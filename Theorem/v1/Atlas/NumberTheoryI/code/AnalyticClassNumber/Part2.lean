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
import Abbrev.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber
open scoped Classical

open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex

open NumberField.InfinitePlace NumberField.Units


noncomputable section

namespace Section19

section DirichletSeries

set_option backward.isDefEq.respectTransparency false in

theorem subgroup_dual_card_annihilator (G : Type*) [CommGroup G] [Fintype G] (H : Subgroup G) :
    Nat.card H * Nat.card (MonoidHom.restrictHom H ℂˣ).ker = Nat.card G := by
  have hsurj := MonoidHom.restrict_surjective (G := G) ℂ H
  have hcard_G : Nat.card (G →* ℂˣ) = Nat.card G :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  have hcard_H : Nat.card (↥H →* ℂˣ) = Nat.card ↥H :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥H ℂ
  have hlagrange := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (MonoidHom.restrictHom H ℂˣ).ker
  have hquot : Nat.card ((G →* ℂˣ) ⧸ (MonoidHom.restrictHom H ℂˣ).ker) = Nat.card (↥H →* ℂˣ) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
  rw [← hcard_G, hlagrange, hquot, hcard_H]

end DirichletSeries
end Section19
end
