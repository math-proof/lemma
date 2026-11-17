/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Structure.v1.Atlas.NumberTheoryI.code.ArtinUnramified


public noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

structure CyclicExtensionData where
  G : Type*
  M : Type*
  [instGroupG : Group G]
  [instFiniteG : Finite G]
  [instCyclicG : IsCyclic G]
  [instCommGroupM : CommGroup M]
  [instFiniteM : Finite M]
  [instAction : MulDistribMulAction G M]
  n : ℕ
  hn_pos : 0 < n
  hn_eq : n = Nat.card G
  ram : RamificationData
  card_ClK : ℕ
  hcard_ClK_pos : 0 < card_ClK
  norm_units_index : ℕ
  hnorm_pos : 0 < norm_units_index
  norm_index_IK : ℕ
  hnorm_index_IK_pos : 0 < norm_index_IK
  h0_ClL : ℕ
  hh0_pos : 0 < h0_ClL
  h_acnf : Nat.card (FixedPoints.subgroup G M) * norm_units_index * n = ram.e * card_ClK
  h_norm_index_ineq : norm_index_IK ≤ n
  h_eq8 : norm_index_IK * ram.e = h0_ClL * norm_units_index * n

end ArtinUnramified
end
