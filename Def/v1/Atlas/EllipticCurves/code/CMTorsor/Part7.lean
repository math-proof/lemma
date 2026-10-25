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
import Structure.v1.Atlas.EllipticCurves.code.CMTorsor.Part3


namespace CMTorsorAction

open IdealTorsion NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- The `𝒪`-linear map `𝒪/𝔟 → 𝒪/targetIdeal` underlying a `CMIsogenyData`. -/
noncomputable def CMIsogenyData.toLinearMap {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) :
    (𝒪 ⧸ (𝔟 : Submodule 𝒪 𝒪)) →ₗ[𝒪] (𝒪 ⧸ (φ.targetIdeal : Submodule 𝒪 𝒪)) :=
  (𝔟 : Submodule 𝒪 𝒪).mapQ φ.targetIdeal LinearMap.id
    (by rw [Submodule.comap_id]; exact φ.le_target)

/-- The degree of the CM-isogeny `φ`, defined as the cardinality of its kernel. -/
noncomputable def degIsogeny {𝔟 𝔞 : Ideal 𝒪} (φ : CMIsogenyData 𝒪 𝔟 𝔞) : ℕ :=
  Nat.card (LinearMap.ker φ.toLinearMap)

end CMTorsorAction
