/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationDivisor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public section

set_option maxHeartbeats 800000

open IsDedekindDomain


/-- Algebraic data for a morphism of smooth curves: a pair of Dedekind domains
`R → S` corresponding to the coordinate rings of the source and target curves. -/
structure CurveMorphismData where
  R : Type*
  S : Type*
  [commRingR : CommRing R]
  [commRingS : CommRing S]
  [isDedekindR : IsDedekindDomain R]
  [isDedekindS : IsDedekindDomain S]
  [algebraRS : Algebra R S]

