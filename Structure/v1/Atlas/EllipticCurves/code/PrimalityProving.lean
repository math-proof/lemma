/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Data.Int.GCD
public import Mathlib.GroupTheory.OrderOfElement
public import Def.v1.Atlas.EllipticCurves.code.PointCounting.Part2
public import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting
public import Def.v1.Atlas.EllipticCurves.code.PrimalityProving
open scoped Nat


public noncomputable section

open Classical

/-- The hypotheses of the Goldwasser-Kilian primality criterion (Theorem 11.13
of Sutherland): `N, M > 1`, `M > (N^{1/4}+1)^2`, `N` coprime to the
discriminant of `W`, the multiple `MP` is zero mod `N`, and `(M/ℓ)P` is
strongly nonzero mod `N` for every prime `ℓ ∣ M`. -/
structure GoldwasserKilianHyp (W : WeierstrassCurve ℤ) (N M : ℕ)
    (zMP : ℤ) (zMlP : ℕ → ℤ) : Prop where
  hN : N > 1
  hM : M > 1
  hMbound : (M : ℝ) > (Real.sqrt (Real.sqrt ↑N) + 1) ^ 2
  hcop : Nat.Coprime N (Int.natAbs W.Δ)
  hzero : IsZeroModN zMP N
  hstrong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → IsStronglyNonzeroModN (zMlP ℓ) N

end
