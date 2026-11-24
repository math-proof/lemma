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
public import Def.v1.Atlas.NumberTheoryI.code.AnalyticClassNumber.Part3
open scoped Classical
open Filter Topology Asymptotics Set MeasureTheory NumberField NNReal Complex
open NumberField.InfinitePlace NumberField.Units


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/AnalyticClassNumber.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace Section19

section DirichletSeries

instance instNumberFieldFixedField (m : ℕ) [NeZero m]
    (H : Subgroup (DirichletCharacter ℂ m)) :
    NumberField (fixedFieldOfCharacterSubgroup m H) :=
  NumberField.of_intermediateField _

end DirichletSeries
end Section19
end
