/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FiniteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Nat.Prime.Basic
import Instance.v1.Atlas.EllipticCurves.code.FiniteFields.Part2


section Definition_3_14

variable (p : ℕ) [Fact p.Prime]

open Polynomial

/-- Definition 3.14: a monic irreducible `f ∈ 𝔽_p[x]` is primitive iff its
adjoined root has order `p^(deg f) - 1` (i.e. generates the multiplicative
group of `𝔽_p[x]/(f)`). -/
def Polynomial.IsPrimitivePolynomial (f : (ZMod p)[X]) : Prop :=
  f.Monic ∧ Irreducible f ∧ orderOf (AdjoinRoot.root f) = p ^ f.natDegree - 1

/-- Theorem 3.9 (data form): for any irreducible `f ∈ 𝔽_p[x]` of positive
degree `n`, the quotient ring `𝔽_p[x]/(f)` is ring-isomorphic to `𝔽_{p^n}`. -/
noncomputable def quotient_irred_ringEquiv_𝔽q
    (f : (ZMod p)[X]) [hf : Fact (Irreducible f)] (hn : f.natDegree ≠ 0) :
    AdjoinRoot f ≃+* 𝔽q p f.natDegree := by


  have hf0 : f ≠ 0 := hf.out.ne_zero
  let pb := AdjoinRoot.powerBasis hf0
  haveI : Fintype (AdjoinRoot f) := Module.fintypeOfFintype pb.basis
  have hcard_adj : Fintype.card (AdjoinRoot f) = p ^ f.natDegree := by
    have := Module.card_fintype pb.basis
    rw [Fintype.card_fin, AdjoinRoot.powerBasis_dim, ZMod.card] at this
    exact this

  haveI : Fintype (𝔽q p f.natDegree) := Fintype.ofFinite _
  have hcard_gf : Fintype.card (𝔽q p f.natDegree) = p ^ f.natDegree := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p f.natDegree hn
  exact FiniteField.ringEquivOfCardEq (hcard_adj.trans hcard_gf.symm)

/-- The `i`-th Conway coefficient of an order polynomial `f` from
Definition 3.16: take `(-1)^(deg f - i)·coeff_i(f)` and reduce to a
natural number in `[0, p)`. -/
noncomputable def conwayCoeff (f : (ZMod p)[X]) (i : ℕ) : ℕ :=
  ZMod.val ((-1 : ZMod p) ^ (f.natDegree - i) * f.coeff i)

/-- The strict lexicographic order on Conway coefficients used to compare two
order polynomials of the same degree, per Definition 3.16. -/
def conwayLT (f g : (ZMod p)[X]) : Prop :=
  ∃ k : ℕ, k < f.natDegree ∧
    conwayCoeff p f k < conwayCoeff p g k ∧
    ∀ j : ℕ, j < k → conwayCoeff p f j = conwayCoeff p g j

/-- Conway compatibility (Definition 3.16): for every proper divisor `m ∣ n`
and every root `α` of `fam m`, `f(α^(n/m)) = 0` holds in the algebraic
closure of `𝔽_p`. -/
def ConwayCompatible
    (fam : ∀ m : ℕ, 0 < m → (ZMod p)[X]) (n : ℕ) (f : (ZMod p)[X]) : Prop :=
  ∀ m : ℕ, ∀ (hm : 0 < m), m < n → m ∣ n →
    ∀ α : AlgebraicClosure (ZMod p),
      (((fam m hm).map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot α) →
        ((f.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))).IsRoot (α ^ (n / m)))

end Definition_3_14
