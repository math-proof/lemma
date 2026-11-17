/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/CMTorsor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Lemma.Complex.Atlas.v1.EllipticCurves.code.ComplexMultiplication
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Class.v1.Atlas.EllipticCurves.code.CMTorsor


public section

namespace CMTorsorAction

open IdealTorsion NormTrace

variable {𝒪 : Type*} [CommRing 𝒪]

/-- Data describing a CM-isogeny `𝒪/𝔟 → 𝒪/targetIdeal` corresponding to multiplication by
an ideal `𝔞`: includes the target ideal (the colon ideal `(𝔟 : 𝔞)`) and the relation
`𝔞 · targetIdeal = 𝔟`. -/
structure CMIsogenyData (𝒪 : Type*) [CommRing 𝒪] (𝔟 : Ideal 𝒪) (𝔞 : Ideal 𝒪) where
  targetIdeal : Ideal 𝒪
  le_target : 𝔟 ≤ targetIdeal
  ideal_mul_target_le : 𝔞 * targetIdeal ≤ 𝔟
  target_eq_colon :
    (targetIdeal : Submodule 𝒪 𝒪) = (𝔟 : Submodule 𝒪 𝒪).colon (𝔞 : Set 𝒪)
  ideal_mul_target_eq : 𝔞 * targetIdeal = 𝔟

end CMTorsorAction
