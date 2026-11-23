/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApplicationsToGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
public import Def.v1.Atlas.Buildings.code.BNPair.ParabolicDefs.Part2
public import Theorem.Nat.NonemptyBruhatCell
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Filter.AtTopBot.Group
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Structure.v1.Atlas.Buildings.code.Building.ApplicationsToGroups.Part3

@[expose] public section

set_option linter.unusedSectionVars false

open ChamberComplex


section TopologicalGroupDefinition

/-- A group action is maximally strongly transitive if, for every apartment $A'$ in
the system and every chamber $C' \subseteq A'$, some $g \in G$ simultaneously
sends $C'$ to the fixed reference chamber $C_0$ and $A'$ to the fixed reference
apartment $A_0$. This is the relevant transitivity hypothesis for maximal
apartment systems in non-spherical buildings. -/
def IsMaximallyStronglyTransitive
    {G : Type*} {X : Type*}
    (act : G → X → X)
    (IsChamber : Set X → Prop)
    (aptSystem : Set (Set X))
    (C₀ : Set X) (A₀ : Set X) : Prop :=
  ∀ A' ∈ aptSystem, ∀ C', IsChamber C' → C' ⊆ A' →
    ∃ g : G, (fun x => act g x) '' C' = C₀ ∧
            (fun x => act g x) '' A' = A₀

end TopologicalGroupDefinition
