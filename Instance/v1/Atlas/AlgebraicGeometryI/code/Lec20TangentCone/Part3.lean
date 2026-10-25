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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec20TangentCone.Part7
open Polynomial


namespace Lec20TangentCone

universe u

variable {R : Type u} [CommRing R]

/-- The additive group structure on the graded piece `𝔪^n / 𝔪^{n+1}`. -/
instance assocGradedPiece.addCommGroup (𝔪 : Ideal R) (n : ℕ) :
    AddCommGroup (assocGradedPiece 𝔪 n) :=
  inferInstanceAs (AddCommGroup (↥(𝔪 ^ n) ⧸ _))

/-- The `R`-module structure on the graded piece `𝔪^n / 𝔪^{n+1}`. -/
instance assocGradedPiece.module (𝔪 : Ideal R) (n : ℕ) :
    Module R (assocGradedPiece 𝔪 n) :=
  inferInstanceAs (Module R (↥(𝔪 ^ n) ⧸ _))

end Lec20TangentCone
