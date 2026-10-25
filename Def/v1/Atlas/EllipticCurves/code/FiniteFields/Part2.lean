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
import Theorem.v1.Atlas.EllipticCurves.code.FiniteFields.Part2


section Def34

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

open Polynomial

/-- `𝔽q p 1` is canonically isomorphic to `𝔽_p = ZMod p` as a `ZMod p`-algebra. -/
noncomputable def 𝔽q_equivZModP : 𝔽q p 1 ≃ₐ[ZMod p] ZMod p :=
  GaloisField.equivZmodP p

end Def34

section Theorem_3_6

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

/-- Theorem 3.6, uniqueness half (data form): a choice of ring isomorphism
between any finite field `K` of cardinality `p^n` and `𝔽q p n`. -/
noncomputable def 𝔽q_ringEquiv_of_card (hn : n ≠ 0)
    (K : Type*) [Field K] [Fintype K] (hK : Fintype.card K = p ^ n) :
    K ≃+* 𝔽q p n := by
  haveI : Fintype (𝔽q p n) := Fintype.ofFinite _
  have hcard : Fintype.card (𝔽q p n) = p ^ n := by
    rw [Fintype.card_eq_nat_card]
    exact GaloisField.card p n hn
  exact FiniteField.ringEquivOfCardEq (hK.trans hcard.symm)

end Theorem_3_6
