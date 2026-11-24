module
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
public import Theorem.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Structure.v1.Atlas.EllipticCurves.code.CMTorsor.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
