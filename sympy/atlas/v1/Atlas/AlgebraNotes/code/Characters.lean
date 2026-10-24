/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Characters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RepresentationTheory.Tannaka
import Mathlib.GroupTheory.ClassEquation
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Data.Matrix.Action
import Mathlib.LinearAlgebra.Matrix.ToLin

universe u

noncomputable section

open Classical

namespace CharacterTheory

open Representation

abbrev HomG {k : Type u} [CommRing k] {G : Type u} [Monoid G]
    {V : Type u} [AddCommMonoid V] [Module k V]
    {W : Type u} [AddCommMonoid W] [Module k W]
    (ρ : Representation k G V) (ψ : Representation k G W) :=
  ρ.IntertwiningMap ψ

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
