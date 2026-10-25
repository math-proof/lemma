/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Isogenies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Squarefree.Basic
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part11
open Polynomial

open scoped Polynomial.Bivariate

universe u v


namespace IsogenyStandardForm

variable {F : Type u} [Field F]

namespace WithCurveData

variable (α : WithCurveData F)

/-- Reflexivity of triple equivalence: every rational map triple is equivalent to
itself. -/
lemma RationalMapTriple.isEquiv_refl {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (t : RationalMapTriple f₁ f₂) : t.IsEquiv t := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [sub_self]

/-- Symmetry of triple equivalence. -/
lemma RationalMapTriple.isEquiv_symm {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    {t₁ t₂ : RationalMapTriple f₁ f₂} (h : t₁.IsEquiv t₂) : t₂.IsEquiv t₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  set I := Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))
  refine ⟨?_, ?_, ?_⟩
  · have : t₂.ψ_x * t₁.ψ_y - t₁.ψ_x * t₂.ψ_y =
      -(t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y) := by ring
    rw [this]; exact I.neg_mem h1
  · have : t₂.ψ_x * t₁.ψ_z - t₁.ψ_x * t₂.ψ_z =
      -(t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) := by ring
    rw [this]; exact I.neg_mem h2
  · have : t₂.ψ_y * t₁.ψ_z - t₁.ψ_y * t₂.ψ_z =
      -(t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) := by ring
    rw [this]; exact I.neg_mem h3

/-- Transitivity of triple equivalence, assuming the ideal `(f₁)` is prime so we
can cancel a non-vanishing component of the middle triple. -/
lemma RationalMapTriple.isEquiv_trans_of_prime {k : Type u} [CommRing k]
    {f₁ f₂ : MvPolynomial (Fin 3) k}
    (hprime : (Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k))).IsPrime)
    {t₁ t₂ t₃ : RationalMapTriple f₁ f₂}
    (h12 : t₁.IsEquiv t₂) (h23 : t₂.IsEquiv t₃) : t₁.IsEquiv t₃ := by
  obtain ⟨h12_xy, h12_xz, h12_yz⟩ := h12
  obtain ⟨h23_xy, h23_xz, h23_yz⟩ := h23
  set I := Ideal.span ({f₁} : Set (MvPolynomial (Fin 3) k)) with hI
  obtain (hx | hy | hz) := t₂.not_all_in_ideal
  · have h13_xy : t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y ∈ I := by
      have key : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) =
        t₁.ψ_x * (t₂.ψ_x * t₃.ψ_y - t₃.ψ_x * t₂.ψ_y) +
        t₃.ψ_x * (t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y) := by ring
      have mem : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_left _ h23_xy) (I.mul_mem_left _ h12_xy)
      exact (hprime.mem_or_mem mem).resolve_left hx
    have h13_xz : t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) =
        t₁.ψ_x * (t₂.ψ_x * t₃.ψ_z - t₃.ψ_x * t₂.ψ_z) +
        t₃.ψ_x * (t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) := by ring
      have mem : t₂.ψ_x * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_left _ h23_xz) (I.mul_mem_left _ h12_xz)
      exact (hprime.mem_or_mem mem).resolve_left hx
    have h13_yz : t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_x * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) =
        t₁.ψ_y * (t₂.ψ_x * t₃.ψ_z - t₃.ψ_x * t₂.ψ_z) +
        t₃.ψ_y * (t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) -
        t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) := by ring
      have mem : t₂.ψ_x * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) ∈ I := by
        rw [key]
        exact I.sub_mem (I.add_mem (I.mul_mem_left _ h23_xz) (I.mul_mem_left _ h12_xz))
          (I.mul_mem_left _ h13_xy)
      exact (hprime.mem_or_mem mem).resolve_left hx
    exact ⟨h13_xy, h13_xz, h13_yz⟩
  · have h13_xy : t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y ∈ I := by
      have key : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) =
        (t₁.ψ_x * t₂.ψ_y - t₂.ψ_x * t₁.ψ_y) * t₃.ψ_y +
        t₁.ψ_y * (t₂.ψ_x * t₃.ψ_y - t₃.ψ_x * t₂.ψ_y) := by ring
      have mem : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_right _ h12_xy) (I.mul_mem_left _ h23_xy)
      exact (hprime.mem_or_mem mem).resolve_left hy
    have h13_yz : t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_y * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) =
        t₁.ψ_y * (t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) +
        t₃.ψ_y * (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) := by ring
      have mem : t₂.ψ_y * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_left _ h23_yz) (I.mul_mem_left _ h12_yz)
      exact (hprime.mem_or_mem mem).resolve_left hy
    have h13_xz : t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) =
        t₁.ψ_x * (t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) +
        t₃.ψ_x * (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) +
        t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) := by ring
      have mem : t₂.ψ_y * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) ∈ I := by
        rw [key]
        exact I.add_mem (I.add_mem (I.mul_mem_left _ h23_yz) (I.mul_mem_left _ h12_yz))
          (I.mul_mem_left _ h13_xy)
      exact (hprime.mem_or_mem mem).resolve_left hy
    exact ⟨h13_xy, h13_xz, h13_yz⟩
  · have h13_xz : t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) =
        (t₁.ψ_x * t₂.ψ_z - t₂.ψ_x * t₁.ψ_z) * t₃.ψ_z +
        t₁.ψ_z * (t₂.ψ_x * t₃.ψ_z - t₃.ψ_x * t₂.ψ_z) := by ring
      have mem : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_right _ h12_xz) (I.mul_mem_left _ h23_xz)
      exact (hprime.mem_or_mem mem).resolve_left hz
    have h13_yz : t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z ∈ I := by
      have key : t₂.ψ_z * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) =
        (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) * t₃.ψ_z +
        t₁.ψ_z * (t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) := by ring
      have mem : t₂.ψ_z * (t₁.ψ_y * t₃.ψ_z - t₃.ψ_y * t₁.ψ_z) ∈ I := by
        rw [key]; exact I.add_mem (I.mul_mem_right _ h12_yz) (I.mul_mem_left _ h23_yz)
      exact (hprime.mem_or_mem mem).resolve_left hz
    have h13_xy : t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y ∈ I := by
      have key : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) =
        t₁.ψ_x * (t₂.ψ_z * t₃.ψ_y - t₃.ψ_z * t₂.ψ_y) -
        t₃.ψ_x * (t₁.ψ_y * t₂.ψ_z - t₂.ψ_y * t₁.ψ_z) +
        t₂.ψ_y * (t₁.ψ_x * t₃.ψ_z - t₃.ψ_x * t₁.ψ_z) := by ring
      have mem : t₂.ψ_z * (t₁.ψ_x * t₃.ψ_y - t₃.ψ_x * t₁.ψ_y) ∈ I := by
        rw [key]
        have h23_zy : t₂.ψ_z * t₃.ψ_y - t₃.ψ_z * t₂.ψ_y ∈ I := by
          have : t₂.ψ_z * t₃.ψ_y - t₃.ψ_z * t₂.ψ_y =
            -(t₂.ψ_y * t₃.ψ_z - t₃.ψ_y * t₂.ψ_z) := by ring
          rw [this]; exact I.neg_mem h23_yz
        exact I.add_mem (I.sub_mem (I.mul_mem_left _ h23_zy) (I.mul_mem_left _ h12_yz))
          (I.mul_mem_left _ h13_xz)
      exact (hprime.mem_or_mem mem).resolve_left hz
    exact ⟨h13_xy, h13_xz, h13_yz⟩

end WithCurveData
end IsogenyStandardForm
