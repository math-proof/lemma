/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part6
open scoped LinearAlgebra.Projectivization


noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial Finsupp

open scoped LinearAlgebra.Projectivization

namespace Corollary1326

variable {n : ℕ} (k : Type*) [Field k]

/-- The affine piece of a projective ideal $I$ over chart $U_0$ equals the
zero locus of its dehomogenization at $X_0$. -/
theorem affinePart_eq_dehomogenizedIdeal_zeroLocus
    (I : Ideal (MvPolynomial (Fin (n + 1)) k)) :
    {P : Fin n → k | ∀ f ∈ I,
      eval ((0 : Fin (n + 1)).insertNth (1 : k) P) f = 0} =
    {P : Fin n → k | ∀ g ∈ I.map (AffineParts.dehomogenize k 0), eval P g = 0} := by
  have h1 := Theorem1324.projective_closure_of_affinePart_eq k I
  have h2 := Theorem1323.projective_closure_cap_affine_eq k
    (I.map (AffineParts.dehomogenize k 0))
  exact h1.trans h2

end Corollary1326
end
