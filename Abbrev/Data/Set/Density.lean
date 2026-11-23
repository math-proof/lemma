/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Density.lean -/

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

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Theorem.Set.ImageIioDiv_2.eq.InterSetOfEven_Iio
public import Theorem.Set.Interval.Finset.Basic
public import Instance.Data.Set.Interval
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Order.Interval.Set.Nat
public import Mathlib.Tactic
@[expose] public section

open Filter

open scoped Topology


namespace Set

/--
Given a set `S` and an element `b` in an order `β`, where all intervals bounded above are finite,
we define the partial density of `S` (relative to a set `A`) to be the proportion of elements in
`{x ∈ A | x < b}` that lie in `S ∩ A`.

This definition was inspired from https://github.com/b-mehta/unit-fractions
-/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

end Set
