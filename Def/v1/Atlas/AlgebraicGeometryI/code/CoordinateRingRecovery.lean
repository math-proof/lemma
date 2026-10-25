/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoordinateRingRecovery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.Polynomial.Basic
open AlgebraicGeometry PrimeSpectrum


section GlobalSections

/-- Theorem 2.1: the global sections of `Spec R` recover `R`, i.e. `Γ(Spec R, O) ≅ R`. -/
noncomputable def globalSections_spec_iso (R : CommRingCat.{u}) :
    Γ(Spec R, ⊤) ≅ R :=
  Scheme.ΓSpecIso R

end GlobalSections
