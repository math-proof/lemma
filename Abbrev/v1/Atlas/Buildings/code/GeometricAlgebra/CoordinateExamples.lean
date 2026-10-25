/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/CoordinateExamples.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Data.Matrix.Block
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.CoordinateExamples
open Matrix


namespace CoordinateExamples

/-- Symplectic condition: `g` preserves the (alternating) form `J`. -/
abbrev IsSymplectic {n : ℕ} {k : Type*} [CommRing k]
    (J : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k) : Prop :=
  IsFormPreserving J g

/-- Split-orthogonal condition: `g` preserves the (symmetric hyperbolic) form `S`. -/
abbrev IsSplitOrthogonal {n : ℕ} {k : Type*} [CommRing k]
    (S : Matrix (Fin n) (Fin n) k) (g : Matrix (Fin n) (Fin n) k) : Prop :=
  IsFormPreserving S g

/-- `(p, q)`-orthogonal condition: `g` preserves the signature `(p, q)` form `Q`. -/
abbrev IsOrthogonalPQ {m : ℕ} {k : Type*} [CommRing k]
    (Q : Matrix (Fin m) (Fin m) k) (g : Matrix (Fin m) (Fin m) k) : Prop :=
  IsFormPreserving Q g

end CoordinateExamples
