/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Morphisms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.ProjectiveVarieties.Part7
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.ProjectiveVarieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.VarietyAlgebraEquiv
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Theorem1324
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
import Theorem.v1.Atlas.ArithmeticGeometry.code.Theorem1324
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Basic
import Mathlib.Topology.Order


noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- A nonzero $(n+1)$-tuple of coordinates in $\bar k$, the underlying data of
a point of projective $n$-space before quotienting by rescaling. -/
def ProjectivePoint (n : ℕ) : Type _ :=
  {v : Fin (n + 1) → AlgebraicClosure k // v ≠ 0}

/-- The equivalence relation on $\bar k^{n+1} \setminus \{0\}$ identifying two
nonzero tuples that differ by a nonzero scalar; the quotient is projective
$n$-space $\mathbb{P}^n(\bar k)$. -/
def projectiveSetoid (n : ℕ) : Setoid (ProjectivePoint k n) where
  r v w := ∃ c : AlgebraicClosure k, c ≠ 0 ∧ ∀ i, v.1 i = c * w.1 i
  iseqv := {
    refl := fun v => ⟨1, one_ne_zero, fun i => by ring⟩
    symm := fun ⟨c, hc, h⟩ =>
      ⟨c⁻¹, inv_ne_zero hc, fun i => by rw [h i, inv_mul_cancel_left₀ hc]⟩
    trans := fun ⟨c, hc, h1⟩ ⟨d, hd, h2⟩ =>
      ⟨c * d, mul_ne_zero hc hd, fun i => by rw [h1, h2]; ring⟩
  }

/-- Projective $n$-space $\mathbb{P}^n(\bar k)$ over the algebraic closure of
$k$, defined as the quotient of $\bar k^{n+1}\setminus\{0\}$ by the scaling
equivalence relation. -/
def ProjectiveSpace_k (n : ℕ) : Type _ :=
  Quotient (projectiveSetoid k n)

/-- The set of $k$-rational points $\mathbb{P}^n(k) \subseteq \mathbb{P}^n(\bar k)$:
those projective points admitting a representative all of whose coordinates lie
in the image of $k \hookrightarrow \bar k$. -/
def ProjectiveSpace_k.kRationalPoints (n : ℕ) : Set (ProjectiveSpace_k k n) :=
  {p | ∃ v : ProjectivePoint k n, Quotient.mk (projectiveSetoid k n) v = p ∧
    ∀ i : Fin (n + 1), ∃ a : k, algebraMap k (AlgebraicClosure k) a = v.1 i}

end
