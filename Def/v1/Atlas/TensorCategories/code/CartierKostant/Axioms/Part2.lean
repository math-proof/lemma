module
public import Theorem.v1.Atlas.TensorCategories.code.HopfAlgebra.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
public import Theorem.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
public import Def.v1.Atlas.TensorCategories.code.CoradicalFiltration.Part8
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.Coalgebra.Hom
public import Mathlib.RingTheory.Smooth.Basic
public import Theorem.v1.Atlas.TensorCategories.code.CartierKostant.Axioms
set_option maxHeartbeats 800000
open Coalgebra HopfAlgebra
open scoped TensorProduct


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u v


/-- The Lie subalgebra `Prim(H)` of primitive elements of a Hopf algebra `H`, with bracket
inherited from the commutator. -/
def HopfAlgebra.primitiveLieSubalgebra : LieSubalgebra R H where
  toSubmodule := HopfAlgebra.primitiveElements (R := R)
  lie_mem' hx hy := HopfAlgebra.IsPrimitive.lie_bracket hx hy

/-- The canonical algebra map `U(Prim(H)) → H` from the universal enveloping algebra of
the Lie algebra of primitive elements into `H`. -/
noncomputable def HopfAlgebra.canonicalMapUEA :
    UniversalEnvelopingAlgebra R (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)) →ₐ[R] H :=
  (UniversalEnvelopingAlgebra.lift R) (HopfAlgebra.primitiveLieSubalgebra (R := R) (H := H)).incl

section UEARange

variable {R : Type u} {H : Type v}

variable [CommRing R] [Ring H] [HopfAlgebra R H]

/-- An element `g` of a Hopf algebra `H` is grouplike if `Δ g = g ⊗ g` and `ε g = 1`. -/
def HopfAlgebra.IsGrouplikeHopf (g : H) : Prop :=
  comul (R := R) g = g ⊗ₜ g ∧ counit (R := R) g = 1

/-- The set of grouplike elements of a Hopf algebra `H`. -/
def HopfAlgebra.grouplikeElements : Set H :=
  {g : H | HopfAlgebra.IsGrouplikeHopf (R := R) g}

/-- Promote a grouplike element to a unit of `H`, using the antipode as its inverse. -/
noncomputable def HopfAlgebra.IsGrouplikeHopf.toUnit {g : H}
    (hg : HopfAlgebra.IsGrouplikeHopf (R := R) g) : Hˣ where
  val := g
  inv := antipode R g
  val_inv := hg.mul_antipode
  inv_val := hg.antipode_mul

end UEARange
