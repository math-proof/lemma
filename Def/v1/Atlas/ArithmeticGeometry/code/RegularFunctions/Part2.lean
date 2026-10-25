/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/RegularFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites
import Theorem.v1.Atlas.ArithmeticGeometry.code.RegularFunctions
open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]


section RegularFunctions

variable {k}

variable {n : ℕ} {X : Set (Fin n → AlgebraicClosure k)}

variable [hdom : IsDomain (AffineCoordinateRingBar X)]

/-- Definition 15.2 (regularity at a point). A rational function
$r \in \bar k(X) = \mathrm{Frac}(\bar k[X])$ is *regular at* $P \in X$ if it can be
written as a fraction $r = f/g$ with $f, g \in \bar k[X]$ and $g(P) \neq 0$.
Equivalently: there exists $g \in \bar k[X]$ with $g(P) \neq 0$ such that $g \cdot r$
lies in the image of $\bar k[X]$ in the fraction field. -/
def IsRegularAt
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k)
    (hP : P ∈ X) : Prop :=
  ∃ g : AffineCoordinateRingBar X,
    evalBarAtPoint k X P hP g ≠ 0 ∧
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))

/-- The *denominator ideal* of a rational function $r \in \bar k(X)$: the ideal of
elements $g \in \bar k[X]$ such that $g \cdot r$ lies in $\bar k[X]$. Its non-vanishing
locus is the regular locus of $r$. -/
noncomputable def denominatorIdeal
    (r : FractionRing (AffineCoordinateRingBar X)) :
    Ideal (AffineCoordinateRingBar X) where
  carrier := {g : AffineCoordinateRingBar X |
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, zero_mul]
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
    obtain ⟨fa, hfa⟩ := ha
    obtain ⟨fb, hfb⟩ := hb
    exact ⟨fa + fb, by rw [map_add, hfa, hfb]⟩
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hg ⊢
    rw [mul_assoc]
    obtain ⟨fg, hfg⟩ := hg
    exact ⟨c * fg, by rw [map_mul, hfg]⟩


/-- The *regular domain* (or *regular locus*) of $r \in \bar k(X)$: the set of points
$P \in X$ at which $r$ is regular. -/
def regularDomain
    (r : FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin n → AlgebraicClosure k) :=
  {P : Fin n → AlgebraicClosure k | ∃ (hP : P ∈ X), IsRegularAt r P hP}

/-- Evaluation of a rational function $r \in \bar k(X)$ at a point $P$ where $r$ is
regular: choose a representation $r = f/g$ with $g(P) \neq 0$ and return
$f(P)/g(P) \in \bar k$. The value is independent of the choice of representation
(though that is not proven here). -/
noncomputable def evalRatFunAt
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt r P hP) : AlgebraicClosure k :=
  let g := hreg.choose
  let hg := hreg.choose_spec
  let f := hg.2.choose
  evalBarAtPoint k X P hP f / evalBarAtPoint k X P hP g

/-- A tuple $(\varphi_1, \dots, \varphi_{n_\mathrm{cod}})$ of rational functions in
$\bar k(X)$ is *regular at $P \in X$* if each component $\varphi_i$ is regular at $P$. -/
def IsTupleRegularAt
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (P : Fin m → AlgebraicClosure k)
    (hP : P ∈ X) : Prop :=
  ∀ i : Fin n_cod, IsRegularAt (φ i) P hP

/-- Componentwise evaluation of a tuple of rational functions at a point of common
regularity: produces a point of $\bar k^{n_\mathrm{cod}}$. -/
noncomputable def evalTupleAt
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt φ P hP) :
    Fin n_cod → AlgebraicClosure k :=
  fun j => evalRatFunAt (φ j) P hP (hreg j)

end RegularFunctions
