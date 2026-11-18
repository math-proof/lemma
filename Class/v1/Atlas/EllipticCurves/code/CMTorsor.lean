module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.FractionalIdeal.Inverse
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Quotient.Card
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.RingTheory.ClassGroup
public import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part6
public section

namespace CMTorsorAction

open IdealTorsion NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- A *CM-module* over `𝒪` is an `𝒪`-module `E` together with the data of an ideal
`latticeIdeal ⊆ 𝒪` and an `𝒪`-linear equivalence `E ≃ₗ[𝒪] 𝒪 / latticeIdeal`. -/
class IsCMModule (𝒪 : Type*) [CommRing 𝒪] (E : Type*) [AddCommGroup E] [Module 𝒪 E] where
  latticeIdeal : Ideal 𝒪
  linearEquiv : E ≃ₗ[𝒪] 𝒪 ⧸ (latticeIdeal : Submodule 𝒪 𝒪)

end CMTorsorAction
