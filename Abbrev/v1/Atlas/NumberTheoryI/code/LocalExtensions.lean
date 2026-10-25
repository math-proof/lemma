/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Order.Hom.Lattice
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Unramified.Basic
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Theorem.v1.Atlas.NumberTheoryI.code.HenselFactorization
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.HenselFactorization
import Def.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part3


section MaxUnramifiedInvariance

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

variable (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

noncomputable abbrev AKLB_ramIdx :=
  (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)

noncomputable abbrev AKLB_resDeg :=
  Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)

end MaxUnramifiedInvariance
