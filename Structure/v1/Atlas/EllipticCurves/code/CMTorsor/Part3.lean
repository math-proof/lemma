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
import Class.v1.Atlas.EllipticCurves.code.CMTorsor


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
