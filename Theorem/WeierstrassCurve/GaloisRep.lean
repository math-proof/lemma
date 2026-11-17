/-
Copyright (c) 2024 Imperial College London FLT project contributors.
Released under Apache 2.0 license.
Adapted from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT).
-/

module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Instance.FLTPrelim_GaloisRep
public import Def.FLTPrelim_GaloisRep

public section

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]


public theorem algEquiv_smul_def (σ : K ≃ₐ[S] K) (P : (W'⁄K).Point) :
    σ • P = Point.map σ.toAlgHom P :=
  rfl


public theorem algEquiv_smul_zsmul (σ : K ≃ₐ[S] K) (m : ℤ) (P : (W'⁄K).Point) :
    σ • (m • P) = m • (σ • P) :=
  (Point.map σ.toAlgHom).map_zsmul m P

public theorem smul_mem_torsionBy {n : ℕ} (σ : K ≃ₐ[S] K) {P : (W'⁄K).Point}
    (hP : P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n) :
    σ • P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n := by
  rw [Submodule.mem_torsionBy_iff] at hP ⊢
  rw [← algEquiv_smul_zsmul, hP, smul_zero]

end WeierstrassCurve.Affine.Point
