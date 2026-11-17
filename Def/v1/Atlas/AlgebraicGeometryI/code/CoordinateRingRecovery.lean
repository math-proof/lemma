/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Polynomial.Basic

@[expose] public section

open AlgebraicGeometry PrimeSpectrum


section GlobalSections

/-- Theorem 2.1: the global sections of `Spec R` recover `R`, i.e. `Γ(Spec R, O) ≅ R`. -/
noncomputable def globalSections_spec_iso (R : CommRingCat.{u}) :
    Γ(Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R

end GlobalSections
