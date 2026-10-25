/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/TwoD.lean -/

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

import Mathlib.LinearAlgebra.Orientation
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Euclidean.Angle.Oriented.Affine
import Mathlib.Geometry.Euclidean.Triangle
import Mathlib.Data.Set.Card
import Mathlib.Analysis.Convex.Independent
import Mathlib.Geometry.Euclidean.Sphere.Basic
import Def.Geometry.Metric.Part2
import Lemma.Set.Metric
import Lemma.Set.Triplewise
import Mathlib.Logic.Equiv.Fin.Rotate
import Def.Data.Set.Triplewise
import Instance.Geometry.TwoD
open scoped EuclideanGeometry Finset

open scoped EuclideanSpace EuclideanGeometry

open scoped Real


namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)] {p : Fin n → P}

/-- We say a subset `A` of points in the plane is non-trilinear
if it contains no three points that lie on the same line. -/
def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/-- We say a subset `S` of points is non-collinear for $n$ points
if it contains no $n$ points that lie on the same line. -/
def NonCollinearFor (n : ℕ) (S : Set P) : Prop :=
  ∀ (A : Set P), A ⊆ S → A.Finite → A.ncard = n → ¬ Collinear ℝ A

/-- The set `P` contains a convex `n`-gon.
See also `IsConvexPolygon`. -/
def HasConvexNGon (n : ℕ) (P : Set ℝ²) : Prop :=
  ∃ S : Finset ℝ², S.card = n ∧ ↑S ⊆ P ∧
    ConvexIndependent ℝ (fun x : (↑S : Set ℝ²) => (x : ℝ²))

/-- The statement that a sequence of points form a counter-clockwise convex polygon. -/
def IsCcwConvexPolygon (p : Fin n → P) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k → (∡ (p i) (p j) (p k)).sign = -1

/-- The statement that a sequence of points form a convex polygon. -/
def IsConvexPolygon {n : ℕ} (p : Fin n → P) : Prop :=
  IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i => p (-i)

/-- The signed oriented area of the triangle with vertices `a b c`: half the value of the
positive orientation area form on the edge vectors. It negates when two vertices are
swapped, and may be negative for clockwise ordering. -/
noncomputable def orientedTriangleArea (a b c : P) : ℝ :=
  positiveOrientation.areaForm (a -ᵥ c) (b -ᵥ c) / 2

/-- Let $x_1,\ldots,x_n\in \mathbb{R}^2$ and let $R(x_i)=\#\{ \lvert x_j-x_i\rvert : j\neq i\}$,
where the points are ordered such that
$$R(x_1)\leq \cdots \leq R(x_n).$$
Let $g(n)$ be the maximum number of distinct values the $R(x_i)$ can take. -/
noncomputable def maximalDistinctDistancesFrom (n : ℕ) : ℕ :=
  sSup {#(X.image (distinctDistancesFrom X)) | (X : Finset ℝ²) (_ : #X = n)}

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is in _general position_
if no three are collinear and no four lie on a circle.

Stated for `Set ℝ²` so that infinite collections are covered; a `Finset` argument coerces. -/
def InGeneralPosition (X : Set ℝ²) : Prop :=
  NonTrilinear X ∧ ∀ T ⊆ X, T.ncard = 4 → ¬Cospherical T

/-- `a b c` are the vertices of a right-angled triangle: the three vertices are pairwise
distinct and the (unoriented) angle at one of the three vertices equals `π / 2`. The
distinctness hypothesis rules out degenerate triples, whose angles can coincide with `π / 2`. -/
def IsRightAngled (a b c : P) : Prop :=
  a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    (∠ b a c = π / 2 ∨ ∠ a b c = π / 2 ∨ ∠ b c a = π / 2)

/--
`a b c d` are the vertices, in counter-clockwise order, of an isosceles trapezoid: they are in
strictly convex position, the side `ab` is parallel to the side `cd` (the two bases), and the
diagonals `ac` and `bd` have equal length. One pair of parallel sides together with equal
diagonals is the classical characterization of an isosceles trapezoid; in particular it rules
out non-rectangular parallelograms.
-/
def IsIsoscelesTrapezoid (a b c d : ℝ²) : Prop :=
  IsCcwConvexPolygon ![a, b, c, d] ∧
  (affineSpan ℝ {a, b}).Parallel (affineSpan ℝ {c, d}) ∧
  dist a c = dist b d

end EuclideanGeometry

def IsIsosceles {α : Type*} [Dist α] (p q r : α) : Prop :=
  dist p q = dist q r ∨ dist q r = dist r p ∨ dist r p = dist p q

nonrec def Set.IsIsosceles {α : Type*} [Dist α] (A : Set α) :=
  Nonempty A ∧ A.Triplewise (IsIsosceles · · ·)

/-- A set is isosceles-free if no three distinct points in it form an isosceles triangle. -/
def Set.IsIsoscelesFree {α : Type*} [Dist α] (A : Set α) : Prop :=
  A.Triplewise fun x y z ↦ ¬ _root_.IsIsosceles x y z

