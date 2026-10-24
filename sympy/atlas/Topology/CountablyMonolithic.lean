/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/CountablyMonolithic.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Topology.Bases

/-- A topological space has a countable network if there is a countable family
of sets refining every open neighborhood of each of its points. Network sets
need not themselves be open. -/
def HasCountableNetwork (X : Type*) [TopologicalSpace X] : Prop :=
  ∃ 𝒩 : Set (Set X), 𝒩.Countable ∧
    ∀ ⦃U : Set X⦄, IsOpen U → ∀ x ∈ U,
      ∃ V ∈ 𝒩, x ∈ V ∧ V ⊆ U

/-- A topological space is countably monolithic (ω-monolithic) if the closure
of every countable subspace has a countable network. -/
class CountablyMonolithicSpace (X : Type*) [TopologicalSpace X] : Prop where
  hasCountableNetwork_closure_of_countable :
    ∀ ⦃s : Set X⦄, s.Countable → HasCountableNetwork ↥(closure s)
