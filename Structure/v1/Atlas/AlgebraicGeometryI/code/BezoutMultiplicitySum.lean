/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/BezoutMultiplicitySum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutLight
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- A point of intersection of the projective varieties `V(f)` and `V(g)`, encoded as a prime
ideal of `k[x, y, z]` containing both `f` and `g`. -/
structure ProjectivePoint (k : Type*) [Field k]
    (f g : MvPolynomial (Fin 3) k) where
  P : Ideal (MvPolynomial (Fin 3) k)
  hP_prime : P.IsPrime
  hf_mem : f ∈ P
  hg_mem : g ∈ P

end
