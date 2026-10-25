/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.TensorAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Coalgebra.Hom
import Mathlib.RingTheory.Smooth.Basic
import Notation.v1.Atlas.TensorCategories.code.CartierKostant.Axioms
set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


section UEARange

variable {R : Type u} {H : Type v}

variable [CommRing R] [Ring H] [HopfAlgebra R H]

local notation "SV" => SymmetricAlgebra k V

/-- The standard comultiplication on the symmetric algebra `S(V)` making it a bialgebra:
the generators are sent to primitives, `v ↦ v ⊗ 1 + 1 ⊗ v`. -/
noncomputable def SymmetricAlgebra.comul : SV →ₐ[k] SV ⊗[k] SV :=
  SymmetricAlgebra.lift
    (Algebra.TensorProduct.includeLeft.toLinearMap.comp (SymmetricAlgebra.ι k (M := V)) +
     Algebra.TensorProduct.includeRight.toLinearMap.comp (SymmetricAlgebra.ι k (M := V)))

/-- A 2-tensor `u ∈ S(V) ⊗ S(V)` is symmetric if it is fixed by the flip. -/
def SymmetricAlgebra.IsSymmetricTensor
    (u : SV ⊗[k] SV) : Prop :=
  (TensorProduct.comm k SV SV) u = u

/-- The cocycle condition for a 2-tensor `u ∈ S(V) ⊗ S(V)` with respect to the standard
comultiplication: `(Δ ⊗ 1) u + u ⊗ 1 = (1 ⊗ Δ) u + 1 ⊗ u` (up to the associator). -/
def SymmetricAlgebra.IsCocycle2
    (u : SV ⊗[k] SV) : Prop :=
  let Δ := (SymmetricAlgebra.comul k V).toLinearMap
  let assoc := (TensorProduct.assoc k SV SV SV)
  LinearMap.rTensor SV Δ u + u ⊗ₜ[k] 1 =
    assoc.symm (LinearMap.lTensor SV Δ u) + assoc.symm (1 ⊗ₜ[k] u)

/-- A 2-tensor `u` is a coboundary if it equals `Δ w - w ⊗ 1 - 1 ⊗ w` for some
`w ∈ S(V)`. -/
def SymmetricAlgebra.IsCoboundary2
    (u : SV ⊗[k] SV) : Prop :=
  ∃ w : SV,
    u = (SymmetricAlgebra.comul k V) w -
      (Algebra.TensorProduct.includeLeft : SV →ₐ[k] SV ⊗[k] SV) w -
      (Algebra.TensorProduct.includeRight : SV →ₐ[k] SV ⊗[k] SV) w

/-- The multiplication map `S(V) ⊗ S(V) → S(V)`, regarded as an algebra map (using
commutativity of `S(V)`). -/
noncomputable def SymmetricAlgebra.mulMap : SV ⊗[k] SV →ₐ[k] SV :=
  Algebra.TensorProduct.lmul' k

/-- The doubling algebra endomorphism of `S(V)` sending each generator `v` to `2v`. -/
noncomputable def SymmetricAlgebra.doubling : SV →ₐ[k] SV :=
  SymmetricAlgebra.lift (2 • SymmetricAlgebra.ι k (M := V))

/-- The set of grouplike elements of a Hopf algebra, packaged as a subtype to carry a
group structure. -/
def HopfAlgebra.GrouplikeGroup (R : Type u) (H : Type v)
    [CommRing R] [Ring H] [HopfAlgebra R H] : Type v :=
  { g : H // HopfAlgebra.IsGrouplikeHopf (R := R) g }

/-- The antipode of a grouplike element is grouplike for the comultiplication:
`Δ(S(g)) = S(g) ⊗ S(g)`. -/
def HopfAlgebra.GrouplikeGroup.val : HopfAlgebra.GrouplikeGroup R H →* H where
  toFun g := g.1
  map_one' := rfl
  map_mul' _ _ := rfl

end UEARange
