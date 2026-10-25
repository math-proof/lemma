/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSheavesCurves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicGeometryI.code.DegreeAdditivity
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.DegreeAdditivity
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.GrothendieckGroup
import Def.v1.Atlas.AlgebraicGeometryI.code.GrothendieckGroup.Part3
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
open scoped TensorProduct


section TorsionDecomposition

variable {R : Type*} [CommRing R] [IsDomain R]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The torsion submodule of `M`: the submodule of elements killed by some non-zero-divisor of `R`.
This realizes Definition 39 (torsion subsheaf) on curves. -/
def torsionSubmodule (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] :
    Submodule R M :=
  Submodule.torsion R M

end TorsionDecomposition

section Saturation

variable {R : Type*} [CommRing R] [IsDomain R]

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The saturation of a submodule `N ⊆ M`: the preimage under `M → M/N` of the torsion
submodule of `M/N`. Realizes Definition 40 (saturation) on curves. -/
def Submodule.saturation (N : Submodule R M) : Submodule R M :=
  Submodule.comap N.mkQ (Submodule.torsion R (M ⧸ N))

/-- The rank of an `R`-module `M` (Definition 41): the `K`-dimension of `K ⊗_R M`, where `K` is
a field over `R` (typically the fraction field). -/
noncomputable def CoherentSheavesCurves.sheafRank
    (M : Type*) [AddCommGroup M] [Module R M] : ℕ :=
  Module.finrank K (K ⊗[R] M)

end Saturation
