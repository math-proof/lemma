/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Metric.lean -/

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

import sympy.atlas.Data.Sym.Sym2
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.MetricSpace.Defs

open scoped Finset

variable {X : Type*} [MetricSpace X]

/-- The multiplicity of the distance `d` determined by `points`, that is, the number of unordered
pairs of distinct points at distance `d` apart. -/
noncomputable def distanceMultiplicity (points : Finset X) (d : ℝ) : ℕ :=
  #(points.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = d) / 2

/-- The number of pairs of points of a finite set `s` in a metric space that are distance 1 apart.
-/
noncomputable def unitDistNum (s : Finset X) : ℕ := distanceMultiplicity s 1

@[simp] theorem unitDistNum_eq_distanceMultiplicity (s : Finset X) :
    unitDistNum s = distanceMultiplicity s 1 := rfl

/-- The set of distances determined by a finite set of points in a metric space. -/
noncomputable def distanceSet (points : Finset X) : Finset ℝ :=
  points.offDiag.image fun (pair : X × X) => dist pair.1 pair.2

/--
Given a finite set of points in a metric space, we define the number of distinct distances
between pairs of points.
-/
noncomputable def distinctDistances (points : Finset X) : ℕ :=
  #(distanceSet points)

variable (X) in
/-- The minimum number of distinct distances determined by a set of `n` points in `X`.
The explicit existence witness prevents an empty candidate set, so the infimum is never
taken silently over `∅` (where `Nat.sInf_empty = 0` would apply). -/
noncomputable def minimalDistinctDistances (n : ℕ) (_ : ∃ points : Finset X, #points = n) : ℕ :=
  sInf {m : ℕ | ∃ points : Finset X, #points = n ∧ distinctDistances points = m}

open Classical in
/-- Given a finite set of points in a metric space, we define the number of distinct distances
between a given point and all other points. -/
noncomputable def distinctDistancesFrom (points : Finset X) (pt : X) : ℕ :=
  #((points.erase pt).image fun x => dist x pt)

open Classical in
/-- The number of unit-distance pairs of a finite set of `n` points is at most $\binom{n}{2}$,
the total number of unordered pairs of distinct points. -/
theorem unitDistNum_le_choose_two (s : Finset X) : unitDistNum s ≤ (#s).choose 2 := by
  unfold unitDistNum distanceMultiplicity
  calc #(s.offDiag.filter fun (pair : X × X) => dist pair.1 pair.2 = 1) / 2
      ≤ #s.offDiag / 2 := Nat.div_le_div_right (Finset.card_filter_le _ _)
    _ = (#s).choose 2 := by
      rw [Finset.offDiag_card, Nat.choose_two_right, Nat.mul_sub_left_distrib, mul_one]
