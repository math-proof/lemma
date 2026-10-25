/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
import Lemma.Nat.NonemptyBruhatCell
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Topology.Algebra.OpenSubgroup
import Def.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part3
set_option linter.unusedSectionVars false

open ChamberComplex


section TopologicalGroupDefinition

/-- Bundle of data witnessing a maximally strongly transitive action of a
topological group $G$ on a building-like set $X$. It records the action, a
reference chamber $C_0 \subseteq A_0$ inside a reference apartment, the
compact-open stabiliser $B$ of $C_0$, the system of maximal apartments and its
$G$-invariance, chamber-transitivity of $G$, and an exhaustion of each apartment
by $B$-conjugable pieces that together force a translating element back into
$A_0$. This is the precise hypothesis package used to prove strong transitivity
on maximal apartment systems. -/
structure MaxStrongTransData (G : Type*) (X : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] where
  act : G → X → X
  act_mul : ∀ g₁ g₂ : G, ∀ x : X, act (g₁ * g₂) x = act g₁ (act g₂ x)
  act_one : ∀ x : X, act 1 x = x
  C₀ : Set X
  A₀ : Set X
  chamber_sub_apt : C₀ ⊆ A₀
  B : Subgroup G
  B_eq_fixer : (B : Set G) = {g | ∀ x ∈ C₀, act g x = x}
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
      (_ : ∀ i, IsOpen {g : G | ∀ y ∈ Y i, act g y = y})
      (_ : ∀ g : G, (∀ x ∈ A', act g x ∈ A₀) →
          (fun x => act g x) '' A' = A₀),
      True

end StrongTransitivity

section CanonicalTranslations

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A canonical translation in an affine Coxeter system: an element of the Coxeter
group that conjugates the set of simple reflections to itself and has infinite
order. Such elements act as translations on the geometric realisation of the
affine apartment. -/
structure CanonicalTranslation (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) (bp : BNPair G M) where
  element : M.Group
  permutes_simples : ∀ s : B_idx,
    ∃ s' : B_idx,
      element * M.toCoxeterSystem.simple s * element⁻¹ =
        M.toCoxeterSystem.simple s'
  infinite_order : ∀ n : ℕ, n ≠ 0 → element ^ n ≠ 1

end CanonicalTranslations

section LeviFiltration

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A descending filtration $P_J = F_0 \supseteq F_1 \supseteq \cdots$ on a standard
parabolic subgroup $P_J$ of a BN-pair, abstracting the Moy-Prasad / Levi
filtrations used in the structure theory of $p$-adic groups. -/
structure LeviFiltration (G : Type*) [Group G] {B_idx : Type*}
    (M : CoxeterMatrix B_idx) where
  bnpair : BNPair G M
  generatorSubset : Set B_idx
  filtration : ℕ → Set G
  level_zero : filtration 0 = bnpair.standardParabolic generatorSubset
  descending : ∀ n : ℕ, filtration (n + 1) ⊆ filtration n

end LeviFiltration
