import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Instance.FLTPrelim_GaloisRep

/-
Copyright (c) 2024 Imperial College London FLT project contributors.
Released under Apache 2.0 license.
Adapted from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT).
-/

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]


variable (S) in
def IsGaloisStable {n : ℕ}
    (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)) : Prop :=
  ∀ (σ : K ≃ₐ[S] K), ∀ x ∈ N, σ • x ∈ N

variable (S) in
def GaloisRepIsIrreducible (W' : Affine R) (n : ℕ) : Prop :=
  Nontrivial (Submodule.torsionBy ℤ (W'⁄K).Point n) ∧
    ∀ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
      IsGaloisStable S N → N = ⊥ ∨ N = ⊤

end WeierstrassCurve.Affine.Point
