/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionFreeDVR.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Module.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-- An explicit basis (with rank) for a finitely generated torsion-free
module over a DVR. -/
noncomputable def dvr_fg_torsionFree_basis (R : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (M : Type*) [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.IsTorsionFree R M] :
    Σ n : ℕ, Module.Basis (Fin n) R M :=
  Module.basisOfFiniteTypeTorsionFree' (R := R)
