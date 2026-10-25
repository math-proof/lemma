/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/Theorem136.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.OrdinarySupersingular
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.EndAlgebra
import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
import Instance.v1.Atlas.EllipticCurves.code.EndAlgebra.Part5
import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Dimension.Finrank
import Instance.v1.Atlas.EllipticCurves.code.Theorem136.Part2
open Module Polynomial
open scoped TensorProduct

universe u


namespace EllipticCurve

variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]

/-- The endomorphism algebra is finite-dimensional over $\mathbb{Q}$: in fact it has dimension
$2$ (cf. `endAlg_finrank_eq_two`), as $\mathrm{End}^0(E)$ is an imaginary quadratic field. -/
@[instance, reducible] noncomputable def EndAlgebra.instFiniteDimensional
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    @FiniteDimensional ℚ (EndAlgebra W) _
      (EndAlgebra.instRing W).toAddCommGroup
      (@Algebra.toModule ℚ (EndAlgebra W) _ _ (EndAlgebra.instAlgebra W)) :=
  (AdjoinRoot.powerBasis (endPoly_ne_zero W)).finite

/-- The square root of the Frobenius discriminant $\sqrt{\Delta_\pi}$ inside the endomorphism
algebra, realised as the adjoined root of $X^2 - \Delta_\pi$. -/
noncomputable def EndAlgebra.sqrtD
    (W : WeierstrassCurve.Affine F) : EndAlgebra W :=
  AdjoinRoot.root (endPoly W)

/-- The Frobenius endomorphism $\pi$ inside the endomorphism algebra, expressed as
$\pi = t/2 + \sqrt{\Delta_\pi}/2$ where $t$ is the trace of Frobenius. This element satisfies
$\pi^2 - t\pi + q = 0$ (Theorem 13.6, the characteristic polynomial of Frobenius). -/
noncomputable def EndAlgebra.frobenius
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) : EndAlgebra W :=
  algebraMap ℚ _ (((Hasse.traceFrobenius W : ℤ) : ℚ) / 2) +
    (1 / 2 : ℚ) • EndAlgebra.sqrtD W

/-- The integer Frobenius discriminant $\Delta_\pi = t^2 - 4q$, where $t$ is the trace of
Frobenius and $q = \#F$. By Hasse's bound this quantity is $\leq 0$ (Section 13.6). -/
noncomputable def frobeniusDiscriminant (W : WeierstrassCurve.Affine F) : ℤ :=
  (Hasse.traceFrobenius W) ^ 2 - 4 * (Fintype.card F : ℤ)

/-- The condition that the Frobenius endomorphism $\pi$ is not an integer scalar, equivalently
that $t^2 \neq 4q$, equivalently that $E/F$ is ordinary in the sense of Theorem 13.6. -/
def frobeniusNotInt (W : WeierstrassCurve.Affine F) : Prop :=
  (Hasse.traceFrobenius W) ^ 2 ≠ 4 * (Fintype.card F : ℤ)

end EllipticCurve
