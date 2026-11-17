/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Characters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.RepresentationTheory.Tannaka
public import Mathlib.GroupTheory.ClassEquation
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.Data.Matrix.Action
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Abbrev.v1.Atlas.AlgebraNotes.code.Characters

@[expose] public section

universe u


noncomputable section

open Classical

namespace CharacterTheory

open Representation

def convolution {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {k : Type*} [CommSemiring k] (φ ψ : G → k) : G → k :=
  fun g => ∑ h : G, φ h * ψ (h⁻¹ * g)

def IsClassFunction {G : Type u} [Group G] {k : Type u} [Field k] (f : G → k) : Prop :=
  ∀ g h : G, f (h * g * h⁻¹) = f g

noncomputable def classInnerProduct {G : Type u} [Group G] [Fintype G] {k : Type u} [Field k]
    [Invertible (Nat.card G : k)] (f₁ f₂ : G → k) : k :=
  (Nat.card G : k)⁻¹ * ∑ g : G, f₁ g * f₂ g⁻¹

noncomputable def repOfFun {k : Type*} [Field k] {G : Type*} [Group G] [Fintype G]
    {V : Type*} [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (f : G → k) : V →ₗ[k] V :=
  ∑ g : G, f g • ρ g

noncomputable def wedderburnIrrep (k : Type u) [Field k] [IsAlgClosed k]
    (G : Type u) [Group G] [Fintype G] [NeZero (Nat.card G : k)]
    {n : ℕ} {d : Fin n → ℕ}
    (e : MonoidAlgebra k G ≃ₐ[k] Π j, Matrix (Fin (d j)) (Fin (d j)) k)
    (i : Fin n) :
    Representation k G (Fin (d i) → k) :=
  ((Matrix.toLinAlgEquiv' (R := k) (n := Fin (d i))).toAlgHom.comp
    ((Pi.evalAlgHom k _ i).comp e.toAlgHom)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of k G)


end CharacterTheory
end
