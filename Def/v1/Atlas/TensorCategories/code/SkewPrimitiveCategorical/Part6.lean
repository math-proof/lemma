/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SkewPrimitiveCategorical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Instance.v1.Atlas.TensorCategories.code.SkewPrimitiveCategorical.Part2

@[expose] public section

set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w


noncomputable section

/-- Corollary 1.27.6: in characteristic zero, a finite-dimensional bialgebra has no nonzero
primitive elements. -/
def residueFieldEquivOfAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [Algebra k H] [Module.Finite k H]
    (I : MaximalSpectrum H) : k ≃ₐ[k] (H ⧸ I.asIdeal) := by
  haveI : IsDomain (H ⧸ I.asIdeal) := Ideal.Quotient.isDomain I.asIdeal
  haveI : Module.Finite k (H ⧸ I.asIdeal) := Module.Finite.quotient k I.asIdeal
  haveI : Algebra.IsIntegral k (H ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ I.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

end
