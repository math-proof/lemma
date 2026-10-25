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
import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part2
open scoped LinearAlgebra.Projectivization


namespace AffinePatch

variable {n : ℕ} (k : Type*) [Field k]

/-- Membership criterion in the patch $U_i$ in terms of an explicit
representative $v \neq 0$. -/
@[simp]
lemma mem_affinePatch_mk (i : Fin (n + 1)) (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    Projectivization.mk k v hv ∈ affinePatch k i ↔ v i ≠ 0 := by
  simp [affinePatch, Projectivization.coordNeZero]

/-- A projective point $p$ lies in $U_i$ iff its canonical representative
`p.rep` has nonzero $i$-th coordinate. -/
lemma mem_affinePatch_iff_rep (i : Fin (n + 1)) (p : ℙ k (Fin (n + 1) → k)) :
    p ∈ affinePatch k i ↔ p.rep i ≠ 0 := by
  conv_lhs => rw [← Projectivization.mk_rep p]
  rw [mem_affinePatch_mk]

/-- Inserting a $1$ at index $i$ produces a nonzero tuple. -/
lemma insertNth_one_ne_zero (i : Fin (n + 1)) (a : Fin n → k) :
    i.insertNth (α := fun _ => k) (1 : k) a ≠ 0 := by
  intro h
  have : i.insertNth (α := fun _ => k) (1 : k) a i = (0 : Fin (n + 1) → k) i := congr_fun h i
  simp [Fin.insertNth_apply_same] at this

end AffinePatch
