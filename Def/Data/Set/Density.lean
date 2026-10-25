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

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Lemma.Set.ImageIioDiv_2.eq.InterSetOfEven_Iio
import Lemma.Set.Interval.Finset.Basic
import Instance.Data.Set.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic
import Abbrev.Data.Set.Density
open Filter

open scoped Topology


namespace Set

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the upper
density of `S` (relative to a set `A`) to be the limsup of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def upperDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.limsup fun (b : β) ↦ S.partialDensity A b

/--
Given a set `S` in an order `β`, where all intervals bounded above are finite, we define the lower
density of `S` (relative to a set `A`) to be the liminf of the partial densities of `S`
(relative to `A`) for `b → ∞`.
-/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  atTop.liminf fun (b : β) ↦ S.partialDensity A b

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
density `α : ℝ` (relative to a set `A`) if the proportion of `x ∈ S` such that `x < n`
in `A` tends to `α` as `n → ∞`.

When `β = ℕ` this by default defines the natural density of a set
(i.e., relative to all of `ℕ`).
-/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

/--
A set `S` in an order `β` where all intervals bounded above are finite is said to have
positive density (relative to a set `A`) if there exists a positive `α : ℝ` such that
`S` has density `α` (relative to a set `A`).
-/
def HasPosDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : Prop :=
  ∃ α > 0, S.HasDensity α A

/--
The two-sided partial natural density of a set of integers, counted inside the interval
`[-N, N]`.
-/
noncomputable def intPartialDensity (S : Set ℤ) (N : ℕ) : ℝ :=
  open scoped Classical in
  (((Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun m => m ∈ S)).card : ℝ) /
    (2 * (N : ℝ) + 1)

/-- A set of integers has two-sided natural density `α`. -/
def HasIntDensity (S : Set ℤ) (α : ℝ) : Prop :=
  Tendsto (fun N : ℕ => S.intPartialDensity N) atTop (𝓝 α)

namespace HasIntDensity

end HasIntDensity

namespace HasDensity

end Set.HasDensity

namespace Nat

end Nat

section LogarithmicDensity

/--
A set `A` of natural numbers has logarithmic density `d` if the sequence
$(1 / \log n) \cdot \sum_{k \in A, k \le n} (1/k)$ converges to `d`.
Logarithmic density is a weaker notion than natural density: if a set has natural density `d`,
then it also has logarithmic density `d`, but the converse is false.
-/
def Set.HasLogDensity (A : Set ℕ) (d : ℝ) : Prop :=
  open scoped Classical in
  Tendsto (fun n : ℕ => (∑ k ≤ n with k ∈ A, (k : ℝ)⁻¹ / .log n : ℝ)) atTop (𝓝 d)

end LogarithmicDensity
end Set
