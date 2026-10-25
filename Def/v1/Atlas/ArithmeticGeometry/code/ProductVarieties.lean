/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic
variable (k : Type*) [Field k]


/-- Embedding $\overline{k}[x_1, \ldots, x_m] \hookrightarrow \overline{k}[x_1, \ldots, x_{m+n}]$
in the first $m$ variables, by renaming via `Fin.castAdd`. -/
noncomputable def embedPolyLeft (m n : ℕ) :
    MvPolynomial (Fin m) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.castAdd n)

/-- Embedding $\overline{k}[y_1, \ldots, y_n] \hookrightarrow \overline{k}[x_1, \ldots, x_{m+n}]$
in the last $n$ variables, by renaming via `Fin.natAdd`. -/
noncomputable def embedPolyRight (m n : ℕ) :
    MvPolynomial (Fin n) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.natAdd m)

/-- Image of a set of polynomials under `embedPolyLeft`. -/
def embedSetLeft (m n : ℕ) (S : Set (MvPolynomial (Fin m) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)) :=
  (embedPolyLeft k m n) '' S

/-- Image of a set of polynomials under `embedPolyRight`. -/
def embedSetRight (m n : ℕ) (S : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + n)) (AlgebraicClosure k)) :=
  (embedPolyRight k m n) '' S

/-- Definition 16.2: the product algebraic set $V(S_X) \times V(S_Y) \subseteq \overline{k}^{m+n}$,
defined as the algebraic set in $\overline{k}^{m+n}$ cut out by the embedded polynomials. -/
def ProductAlgebraicSet (m n : ℕ)
    (S_X : Set (MvPolynomial (Fin m) (AlgebraicClosure k)))
    (S_Y : Set (MvPolynomial (Fin n) (AlgebraicClosure k))) :
    Set (AffineSpace_k k (m + n)) :=
  AlgebraicSet k (m + n) (embedSetLeft k m n S_X ∪ embedSetRight k m n S_Y)

/-- Projection $\overline{k}^{m+n} \to \overline{k}^m$ onto the first $m$ coordinates. -/
def projLeft (m n : ℕ) (P : AffineSpace_k k (m + n)) : AffineSpace_k k m :=
  P ∘ Fin.castAdd n

/-- Projection $\overline{k}^{m+n} \to \overline{k}^n$ onto the last $n$ coordinates. -/
def projRight (m n : ℕ) (P : AffineSpace_k k (m + n)) : AffineSpace_k k n :=
  P ∘ Fin.natAdd m

/-- The Cartesian product $X \times Y \subseteq \overline{k}^{m+n}$ as a set, defined by the
projection criteria. -/
def CartesianProduct (m n : ℕ)
    (X : Set (AffineSpace_k k m)) (Y : Set (AffineSpace_k k n)) :
    Set (AffineSpace_k k (m + n)) :=
  {P | projLeft k m n P ∈ X ∧ projRight k m n P ∈ Y}

/-- Partial evaluation of a polynomial in $m+n$ variables by fixing the last $n$ variables to
the values $b \in \overline{k}^n$, returning a polynomial in the first $m$ variables. -/
noncomputable def partialEvalRight (m n : ℕ) (b : AffineSpace_k k n) :
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) →+*
    MvPolynomial (Fin m) (AlgebraicClosure k) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (m + n) =>
      if h : i.val < m
      then MvPolynomial.X ⟨i.val, h⟩
      else MvPolynomial.C (b ⟨i.val - m, by omega⟩))

/-- Partial evaluation of a polynomial in $m+n$ variables by fixing the first $m$ variables
to the values $a \in \overline{k}^m$, returning a polynomial in the last $n$ variables. -/
noncomputable def partialEvalLeft (m n : ℕ) (a : AffineSpace_k k m) :
    MvPolynomial (Fin (m + n)) (AlgebraicClosure k) →+*
    MvPolynomial (Fin n) (AlgebraicClosure k) :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (m + n) =>
      if h : i.val < m
      then MvPolynomial.C (a ⟨i.val, h⟩)
      else MvPolynomial.X ⟨i.val - m, by omega⟩)

/-- The $\overline{k}$-vanishing ideal of a subset $V \subseteq \overline{k}^n$: polynomials
in $\overline{k}[x_1, \ldots, x_n]$ that vanish on $V$. -/
def vanishingIdeal_kbar (n : ℕ) (V : Set (AffineSpace_k k n)) :
    Ideal (MvPolynomial (Fin n) (AlgebraicClosure k)) where
  carrier := {f | ∀ P ∈ V, MvPolynomial.eval P f = 0}
  add_mem' := by
    intro a b ha hb P hP
    simp [ha P hP, hb P hP]
  zero_mem' := by intro P _; simp
  smul_mem' := by intro c f hf P hP; simp [hf P hP]

