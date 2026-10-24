/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.Basic
import Mathlib.Data.Fintype.BigOperators

set_option linter.unusedSectionVars false

open Finset BigOperators CoxeterGroup

namespace TitsCone

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- The **Coxeter wall** $H_s = \{\varphi : \varphi_s = 0\}$ associated to a simple reflection $s$. -/
def coxeterWall (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s = 0}

/-- The positive half-space $H_s^+ = \{\varphi : \varphi_s > 0\}$ cut out by the wall $H_s$. -/
def coxeterUpperHalf (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s > 0}

/-- The negative half-space $H_s^- = \{\varphi : \varphi_s < 0\}$ cut out by the wall $H_s$. -/
def coxeterLowerHalf (_M : CoxeterMatrix B) (s : B) : Set (B → ℝ) :=
  {φ | φ s < 0}

/-- The **open fundamental chamber** $C = \bigcap_s H_s^+ = \{\varphi : \forall s, \varphi_s > 0\}$. -/
def titsFundamentalChamber (_M : CoxeterMatrix B) : Set (B → ℝ) :=
  {φ | ∀ s, φ s > 0}

/-- The **standard face** of type $I \subseteq B$: $F_I = \{\varphi : \varphi_s = 0 \text{ for } s \in I,
\ \varphi_s > 0 \text{ for } s \notin I\}$. -/
def titsFaceDual (_M : CoxeterMatrix B) (I : Finset B) : Set (B → ℝ) :=
  {φ | (∀ s ∈ I, φ s = 0) ∧ (∀ s, s ∉ I → φ s > 0)}

/-- The **contragredient action** of a simple reflection $s$ on coordinates:
$\sigma^*_s(x)_t = x_t - 2 x_s \cdot B(\alpha_s, \alpha_t)$. -/
noncomputable def dualSigma (M : CoxeterMatrix B) (s : B) (x : B → ℝ) : B → ℝ :=
  fun t => x t - 2 * x s * formVal M s t

/-- The **closed fundamental chamber** $\overline{C} = \{\varphi : \forall s, \varphi_s \ge 0\}$. -/
def titsFundamentalClosure (_M : CoxeterMatrix B) : Set (B → ℝ) :=
  {φ | ∀ s, φ s ≥ 0}

/-- The **Tits cone** $\mathcal U = W \cdot \overline{C}$: $W$-orbit of the closed fundamental
chamber under the contragredient action. -/
def titsConeSet (M : CoxeterMatrix B) : Set (B → ℝ) :=
  {x | ∃ (y : B → ℝ), (∀ s, y s ≥ 0) ∧
    ∃ (ws : List B), x = ws.foldl (fun v s => dualSigma M s v) y}

/-- $\overline{C} \subseteq \mathcal U$: the closed fundamental chamber is in the Tits cone
(realized as the orbit of $\overline{C}$ under the empty word). -/
theorem titsFundamentalClosure_subset_titsCone (M : CoxeterMatrix B) :
    titsFundamentalClosure M ⊆ titsConeSet M := by
  intro x hx
  simp only [titsConeSet, Set.mem_setOf_eq, titsFundamentalClosure, Set.mem_setOf_eq] at *
  exact ⟨x, hx, [], rfl⟩

/-- The dual action is an involution: $\sigma^*_s \circ \sigma^*_s = \mathrm{id}$. -/
theorem dualSigma_involutive (M : CoxeterMatrix B) (s : B) (x : B → ℝ) :
    dualSigma M s (dualSigma M s x) = x := by
  ext t
  simp only [dualSigma, formVal_diag]
  ring

end TitsCone

namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

/-- A symmetric matrix $f$ is **indecomposable** iff no proper subset $\emptyset \ne I \subsetneq B$
is "block-diagonal": every such $I$ has a nonzero off-block entry $f_{ij} \ne 0$ with $i \in I$, $j \notin I$. -/
def FormIndecomposable (f : B → B → ℝ) : Prop :=
  ∀ (I : Finset B), I.Nonempty → I ≠ Finset.univ →
    ∃ i ∈ I, ∃ j, j ∉ I ∧ f i j ≠ 0


/-- The **Perron–Frobenius property** for an indecomposable PSD off-diagonal-nonpositive form:
the kernel is 1-dimensional and spanned by a strictly positive vector $v > 0$. -/
class PerronFrobeniusProperty {B : Type*} [Fintype B] (f : B → B → ℝ) : Prop where
  kernel_span :
    CoxeterGroup.FormIndecomposable f →
    (∀ v : B → ℝ, ∑ s, ∑ t, v s * f s t * v t ≥ 0) →
    (∃ v : B → ℝ, v ≠ 0 ∧ ∑ s, ∑ t, v s * f s t * v t = 0) →
    (∀ s t, s ≠ t → f s t ≤ 0) →
    ∃ v : B → ℝ, (∀ s, v s > 0) ∧
      (∀ w : B → ℝ, (∑ s, ∑ t, w s * f s t * w t = 0) →
        ∃ c : ℝ, w = fun b => c * v b)

/-- Hypothesis class encoding the Coxeter classification theorem: a positive-definite Coxeter form
implies the underlying Coxeter group is **finite** (spherical type). Used as an axiom locally to
avoid invoking the full classification. -/
class SphericalFiniteProperty {B : Type*} [DecidableEq B] [Fintype B]
    (M : CoxeterMatrix B) : Prop where
  finite_of_pos_def :
    (∀ v : B → ℝ, v ≠ 0 → CoxeterGroup.bilinForm M v v > 0) → Finite (M.Group)

/-- Restriction of a Coxeter matrix $M$ to the parabolic subset $I \subseteq B$ of generators. -/
def CoxeterMatrix.restrict (M : CoxeterMatrix B) (I : Finset B) : CoxeterMatrix ↥I where
  M := fun ⟨i, _⟩ ⟨j, _⟩ => M i j
  isSymm := by ext ⟨i, _⟩ ⟨j, _⟩; simp [Matrix.transpose, M.symmetric]
  diagonal := by intro ⟨i, _⟩; simp
  off_diagonal := by
    intro ⟨i, _⟩ ⟨j, _⟩ h
    exact M.off_diagonal _ _ (fun heq => h (Subtype.ext heq))

/-- Extend a vector $v : I \to \mathbb R$ to all of $B \to \mathbb R$ by setting components outside $I$ to zero. -/
noncomputable def extendByZero (I : Finset B) (v : ↥I → ℝ) : B → ℝ :=
  fun b => if h : b ∈ I then v ⟨b, h⟩ else 0

end CoxeterGroup
