/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec20TangentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.ReesAlgebra
import Mathlib.AlgebraicGeometry.Scheme
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part3
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The extended ideal `reesIdealFromBase I` is preserved (in the comap sense) by every
scaling endomorphism of the Rees algebra. -/
lemma reesIdealFromBase_le_comap_scaleOnRees (I : Ideal R) (c : R) :
    reesIdealFromBase I ≤ (reesIdealFromBase I).comap (scaleOnRees I c) := by
  unfold reesIdealFromBase
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  show scaleOnRees I c (algebraMap R (reesAlgebra I) r) ∈
    Ideal.map (algebraMap R (reesAlgebra I)) I
  rw [scaleOnRees_algebraMap]
  exact Ideal.mem_map_of_mem _ hr

end Lec20TangentCone
