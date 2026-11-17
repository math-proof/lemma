/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProjectiveVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.KrullDimension
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Abbrev.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part2

@[expose] public section

open scoped LinearAlgebra.Projectivization


namespace AffinePatch

variable {n : ℕ} (k : Type*) [Field k]

/-- Well-defined predicate on a projective point $p \in \mathbb{P}^n(k)$: "the
$i$-th coordinate of any representative of $p$ is nonzero". -/
def Projectivization.coordNeZero (i : Fin (n + 1)) : ℙ k (Fin (n + 1) → k) → Prop :=
  Projectivization.lift
    (fun v => (v : Fin (n + 1) → k) i ≠ 0)
    (by
      intro ⟨a, ha⟩ ⟨b, hb⟩ t hab
      simp only at hab ⊢
      have heq : a i = t * b i := by
        have := congr_fun hab i; simp [Pi.smul_apply, smul_eq_mul] at this; exact this
      have ht : t ≠ 0 := by intro h; apply ha; rw [hab]; simp [h]
      exact propext ⟨fun hai hbi => hai (by rw [heq, hbi, mul_zero]),
                     fun hbi hai => hbi (by rwa [heq, mul_eq_zero, or_iff_right ht] at hai)⟩)

/-- The standard affine patch $U_i = \{[x_0 : \cdots : x_n] \in \mathbb{P}^n(k)
\mid x_i \neq 0\}$. -/
def affinePatch (i : Fin (n + 1)) : Set (ℙ k (Fin (n + 1) → k)) :=
  {p | Projectivization.coordNeZero k i p}

end AffinePatch
