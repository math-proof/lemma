/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
import Def.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part6


noncomputable section

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
