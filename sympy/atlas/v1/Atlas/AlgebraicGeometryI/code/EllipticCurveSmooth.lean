/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/EllipticCurveSmooth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Tactic

open Polynomial
open scoped Polynomial.Bivariate

namespace EllipticCurveSmooth

variable {k : Type*} [Field k]

/-- The short Weierstrass curve `y² = x³ + a x + b` packaged as a `WeierstrassCurve`. -/
noncomputable def shortWeierstrass (a b : k) : WeierstrassCurve k where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := a
  a₆ := b

/-- The bivariate Weierstrass polynomial `Y² − (X³ + aX + b)`, viewed in `k[X][Y]`. -/
noncomputable def weierstrass (a b : k) : Polynomial (Polynomial k) :=
  Polynomial.X ^ 2 -
    Polynomial.C (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b)

/-- Our hand-written Weierstrass polynomial agrees with the mathlib affine
defining polynomial. -/
lemma weierstrass_eq_polynomial (a b : k) :
    weierstrass a b = (shortWeierstrass a b).toAffine.polynomial := by
  unfold weierstrass shortWeierstrass WeierstrassCurve.Affine.polynomial
      WeierstrassCurve.toAffine
  simp only [map_zero, map_add, map_mul, zero_mul, add_zero]

/-- The Weierstrass polynomial is monic of degree two in `Y`. -/
lemma weierstrass_monic (a b : k) : (weierstrass a b).Monic := by
  unfold weierstrass
  apply Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow 2)
  calc (Polynomial.C (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X + Polynomial.C b) :
      Polynomial (Polynomial k)).degree
      ≤ 0 := Polynomial.degree_C_le
    _ < (Polynomial.X ^ 2 : Polynomial (Polynomial k)).degree := by simp

/-- The Weierstrass polynomial has `Y`-degree exactly two. -/
lemma weierstrass_natDegree (a b : k) : (weierstrass a b).natDegree = 2 := by
  unfold weierstrass; compute_degree!

/-- No polynomial in `X` can be a root of the Weierstrass polynomial, by
degree-counting: `X³ + aX + b` has odd degree and so is not a square. -/
lemma weierstrass_no_root (a b : k) (g : Polynomial k) :
    ¬(weierstrass a b).IsRoot g := by
  unfold weierstrass
  simp only [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]
  intro h
  have hdeg : (Polynomial.X ^ 3 + Polynomial.C a * Polynomial.X +
      Polynomial.C b : Polynomial k).natDegree = 3 := by
    compute_degree!
  rw [← h] at hdeg
  have hg_ne : g ≠ 0 := by intro hg0; subst hg0; simp at hdeg
  rw [Polynomial.natDegree_pow g 2] at hdeg
  omega

/-- The Weierstrass polynomial is irreducible in `k[X][Y]`, hence the cubic
defines an integral plane curve. -/
theorem weierstrass_irreducible (a b : k) : Irreducible (weierstrass a b) := by
  have hm := weierstrass_monic a b
  have h2 : 2 ≤ (weierstrass a b).natDegree := by rw [weierstrass_natDegree]
  have h3 : (weierstrass a b).natDegree ≤ 3 := by rw [weierstrass_natDegree]; norm_num
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three h2 h3,
      Multiset.eq_zero_iff_forall_notMem]
  intro x
  rw [Polynomial.mem_roots hm.ne_zero]
  exact weierstrass_no_root a b x

/-- The coordinate ring `k[X][Y]/(Y² − X³ − aX − b)` of the affine Weierstrass
curve is an integral domain. -/
noncomputable instance weierstrass_coordinate_ring_isDomain (a b : k) :
    IsDomain (AdjoinRoot (weierstrass a b)) :=
  AdjoinRoot.isDomain_of_prime (Irreducible.prime (weierstrass_irreducible a b))

/-- Ring equivalence between our coordinate ring and the mathlib affine
coordinate ring, transporting via `weierstrass_eq_polynomial`. -/
noncomputable def coordinateRingEquiv (a b : k) :
    AdjoinRoot (weierstrass a b) ≃+*
      AdjoinRoot (shortWeierstrass a b).toAffine.polynomial :=
  RingEquiv.cast (by rw [weierstrass_eq_polynomial])
