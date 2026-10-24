/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/CartierKostant/Axioms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.CoradicalFiltration
import sympy.atlas.v1.Atlas.TensorCategories.code.CoradicalFiltration
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

set_option maxHeartbeats 800000

open Coalgebra HopfAlgebra
open scoped TensorProduct

universe u v


/-- A coalgebra `(H, Δ, ε)` is cocommutative if the comultiplication is symmetric:
`τ ∘ Δ = Δ` for the flip `τ : H ⊗ H → H ⊗ H`. -/
class Coalgebra.IsCocommutative (R : Type u) (H : Type v)
    [CommSemiring R] [AddCommMonoid H] [Module R H] [Coalgebra R H] : Prop where
  cocomm : (TensorProduct.comm R H H).toLinearMap ∘ₗ (comul : H →ₗ[R] H ⊗[R] H) = comul

/-- An element `x` of a bialgebra `H` is primitive if `Δ x = x ⊗ 1 + 1 ⊗ x`. -/
def HopfAlgebra.IsPrimitive (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ 1 + 1 ⊗ₜ x

/-- The submodule of primitive elements of a bialgebra `H` over `R`. -/
def HopfAlgebra.primitiveElements : Submodule R H where
  carrier := {x : H | HopfAlgebra.IsPrimitive (R := R) x}
  add_mem' {x y} (hx : HopfAlgebra.IsPrimitive x) (hy : HopfAlgebra.IsPrimitive y) := by
    show HopfAlgebra.IsPrimitive (R := R) (x + y)
    unfold HopfAlgebra.IsPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    show HopfAlgebra.IsPrimitive (R := R) 0
    simp [HopfAlgebra.IsPrimitive, TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x (hx : HopfAlgebra.IsPrimitive x) := by
    show HopfAlgebra.IsPrimitive (R := R) (r • x)
    unfold HopfAlgebra.IsPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

/-- The Lie bracket of two primitive elements is primitive, so primitive elements form a
Lie subalgebra. -/
theorem HopfAlgebra.IsPrimitive.lie_bracket {x y : H}
    (hx : HopfAlgebra.IsPrimitive (R := R) x)
    (hy : HopfAlgebra.IsPrimitive (R := R) y) :
    HopfAlgebra.IsPrimitive (R := R) ⁅x, y⁆ := by
  rw [Ring.lie_def]
  unfold HopfAlgebra.IsPrimitive at *
  rw [map_sub, Bialgebra.comul_mul, Bialgebra.comul_mul, hx, hy]
  simp only [mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul,
    TensorProduct.sub_tmul, TensorProduct.tmul_sub]
  abel

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

end PrimitiveLieAlgebra


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

end GrouplikeGroup


/-- The smash product algebra `k[G] ⋉ U(𝔤)` of the group algebra of `G` and the universal
enveloping algebra of a Lie algebra `𝔤`, when `G` acts on `𝔤` by Lie automorphisms. -/
section SmashProductIso

variable (k : Type u) (H : Type v)
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Ring H] [HopfAlgebra k H]
variable [Coalgebra.IsCocommutative k H]

/-- Conjugation action of the grouplike group of `H` on the Lie algebra `Prim(H)` of
primitive elements: `g · x := g x g^{-1}`. -/
end SmashProductIso
