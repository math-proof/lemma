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

import Theorem.Data.Sym.Sym2
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Sym.Card
import Mathlib.Order.Lattice.Nat
import Mathlib.Topology.MetricSpace.Defs
import Theorem.Geometry.Metric
open scoped Finset

variable {X : Type*} [MetricSpace X]


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

