/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Card
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.ClassGroup
import Def.v1.Atlas.EllipticCurves.code.ComplexMultiplication.Part6
import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.EllipticCurves.code.CMTorsor.Part6


namespace CMTorsorAction

open IdealTorsion NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- A *CM-module* over `𝒪` is an `𝒪`-module `E` together with the data of an ideal
`latticeIdeal ⊆ 𝒪` and an `𝒪`-linear equivalence `E ≃ₗ[𝒪] 𝒪 / latticeIdeal`. -/
class IsCMModule (𝒪 : Type*) [CommRing 𝒪] (E : Type*) [AddCommGroup E] [Module 𝒪 E] where
  latticeIdeal : Ideal 𝒪
  linearEquiv : E ≃ₗ[𝒪] 𝒪 ⧸ (latticeIdeal : Submodule 𝒪 𝒪)

end CMTorsorAction
