/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.ApplicationsToGroups
import Lemma.Nat.TopologicalGroupDef
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Topology Filter

section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by $g$ as a self-homeomorphism of a topological group $G$. -/
def conjHomeomorph (g : G) : G ≃ₜ G where
  toEquiv := MulAut.conj g
  continuous_toFun := by
    show Continuous (fun x => g * x * g⁻¹)
    exact (continuous_const.mul continuous_id).mul continuous_const
  continuous_invFun := by
    show Continuous (fun x => g⁻¹ * x * g)
    exact (continuous_const.mul continuous_id).mul continuous_const

/-- The conjugate $gSg^{-1}$ of a subset $S \subseteq G$. -/
def conjSet (g : G) (S : Set G) : Set G :=
  (conjHomeomorph g) '' S

/-- The pointwise fixer of a subset $Y \subseteq X$ under a group action:
the set of group elements that fix every point of $Y$. -/
def pointwiseFixer {G : Type*} {X : Type*} (act : G → X → X) (Y : Set X) : Set G :=
  {g : G | ∀ y ∈ Y, act g y = y}

/-- A bundle of data abstracting a thick building $X$ with a strongly
transitive topological group action: the action and base chamber $C_0
\subseteq A_0$, a compact-open Borel $B$ that fixes $C_0$ pointwise, the
notion of chamber, the maximal apartment system, chamber transitivity, and
exhaustion data for each apartment. -/
structure ThickBuildingData (G : Type*) (X : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] where
  act : G → X → X
  act_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x)
  act_one : ∀ x : X, act 1 x = x
  C₀ : Set X
  A₀ : Set X
  chamber_sub_apt : C₀ ⊆ A₀
  B : Subgroup G
  B_eq_fixer : (B : Set G) = pointwiseFixer act C₀
  B_compact : IsCompact (B : Set G)
  B_open : IsOpen (B : Set G)
  IsChamber : Set X → Prop
  C₀_is_chamber : IsChamber C₀
  maxAptSystem : Set (Set X)
  A₀_in_max : A₀ ∈ maxAptSystem
  maxAptSystem_invariant : ∀ (g : G) (A' : Set X),
    A' ∈ maxAptSystem → (fun x => act g x) '' A' ∈ maxAptSystem
  apt_contains_chamber : ∀ A' ∈ maxAptSystem, ∃ C', IsChamber C' ∧ C' ⊆ A'
  chamber_transitive : ∀ C', IsChamber C' → ∃ h : G,
    (fun x => act h x) '' C₀ = C'
  exhaustion_data : ∀ A' ∈ maxAptSystem, C₀ ⊆ A' →
    ∃ (Y : ℕ → Set X)
      (_ : ∀ i, Y i ⊆ Y (i + 1))
      (_ : C₀ ⊆ Y 0)
      (_ : A' = ⋃ i, Y i)
      (A_chain : ℕ → Set X)
      (_ : ∀ i, Y i ⊆ A_chain i)
      (b : ℕ → G)
      (_ : ∀ i, b i ∈ B)
      (_ : ∀ i, ∀ x ∈ A_chain i, act (b i) x ∈ A₀)
      (_ : ∀ i j, i ≤ j → Y i ⊆ A_chain j)
      (_ : ∀ i, IsOpen (pointwiseFixer act (Y i)))
      (_ : ∀ g : G, (∀ x ∈ A', act g x ∈ A₀) →
          (fun x => act g x) '' A' = A₀),
      True
