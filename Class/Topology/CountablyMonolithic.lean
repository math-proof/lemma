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
import Def.Topology.CountablyMonolithic


/-- A topological space is countably monolithic (ω-monolithic) if the closure
of every countable subspace has a countable network. -/
class CountablyMonolithicSpace (X : Type*) [TopologicalSpace X] : Prop where
  hasCountableNetwork_closure_of_countable :
    ∀ ⦃s : Set X⦄, s.Countable → HasCountableNetwork ↥(closure s)

