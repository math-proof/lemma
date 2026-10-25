/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/GroupApplicationsCh17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part4
import Lemma.Nat.TopologicalGroupDef
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group
import Def.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Set Topology Filter


section Conjugation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

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

end Conjugation
