/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum


section

namespace MetaMathlibExt

open scoped BigOperators

/-- Lattice cells in ambient dimension `d`, as integer points `Fin d → ℤ`.

Source: Sebastian Luther and Stephan Mertens, *The Perimeter of Proper
Polycubes*, Journal of Integer Sequences 20 (2017), Article 17.9.5,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mertens/mert4.tex>:
a `d`-dimensional polycube is a set of face-connected cells in `ℤ^d`,
lines 115–117 (also arXiv:1705.03688v1). -/
def latticeCell (d : ℕ) : Type := Fin d → ℤ

/-- Face adjacency of lattice cells: agreement in every coordinate except one
axis `k`, where the coordinates differ by exactly one.

This is the "neighbors in the polycube" relation underlying the adjacency graph
in Luther–Mertens (JIS 20 (2017), Article 17.9.5, lines 277–279: two vertices
are connected if the corresponding cells are neighbors). -/
def faceAdjacent (d : ℕ) (x y : latticeCell d) : Prop :=
  ∃ k : Fin d, (∀ j : Fin d, j ≠ k → x j = y j) ∧ (y k = x k + 1 ∨ x k = y k + 1)

/-- A polycube as a nonempty finite cell set connected through face adjacency.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 115–117:
a `d`-dimensional polycube is a set of face-connected cells in `ℤ^d`.
Connectivity is expressed by reflexive transitive closure of face adjacency
restricted to the set `S`. -/
def isPolycubeCells (d : ℕ) (S : Finset (latticeCell d)) : Prop :=
  S.Nonempty ∧ ∀ x ∈ S, ∀ y ∈ S,
    Relation.ReflTransGen
      (fun a b : latticeCell d => faceAdjacent d a b ∧ a ∈ S ∧ b ∈ S) x y

/-- Canonical representative of a fixed translation class: every coordinate
minimum is translated to zero.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 115–117:
fixed polycubes are identified up to translation. Each class has a unique
representative with minima at zero. Only translations are quotiented, so
rotations and reflections stay distinct orientations. -/
def isCanonicalCells (d : ℕ) (S : Finset (latticeCell d)) : Prop :=
  ∀ k : Fin d, (∃ x ∈ S, x k = 0) ∧ ∀ x ∈ S, 0 ≤ x k

/-- Proper dimension: the number of coordinate axes on which the canonical cell
set varies.

Source: Luther–Mertens, JIS 20 (2017), Article 17.9.5, lines 160–162:
a polycube spanning `i` dimensions is proper in `i` dimensions.
Asinowski–Barequet–Barequet–Rote, *Proper n-Cell Polycubes in n−3 Dimensions*,
Journal of Integer Sequences 15 (2012), Article 12.8.4, lines 171–172:
proper dimension is the dimension of the convex hull of cell centers, which for
axis-aligned cells equals the count of varying axes. -/
noncomputable def properDimension (d : ℕ) (S : Finset (latticeCell d)) : ℕ :=
  Nat.card { k : Fin d // ∃ x ∈ S, ∃ y ∈ S, x k ≠ y k }

/-- Fixed `n`-cell polycubes in dimension `d`, as canonical representatives:
nonempty finite face-connected sets of cardinality `n` with minima at zero. -/
def fixedPolycube (d n : ℕ) : Type :=
  { S : Finset (latticeCell d) // isPolycubeCells d S ∧ S.card = n ∧ isCanonicalCells d S }

/-- `A_d(n)`: number of fixed `n`-cell polycubes in dimension `d`, counted as
`Nat.card` of canonical representatives. -/
noncomputable def fixedPolycubeCount (d n : ℕ) : ℕ :=
  Nat.card (fixedPolycube d n)

/-- Proper fixed `n`-cell polycubes in proper dimension `i`: canonical
representatives in host dimension `i` whose varying-axis count equals `i`. -/
def properFixedPolycube (n i : ℕ) : Type :=
  { P : fixedPolycube i n // properDimension i P.val = i }

/-- `DX(n,i)`: number of fixed `n`-cell polycubes proper in dimension `i`,
counted as `Nat.card` of canonical representatives. Asinowski et al., JIS 15
(2012), Article 12.8.4, line 978, state `DX(n,0) = 0` for `n > 1`. -/
noncomputable def properFixedPolycubeCount (n i : ℕ) : ℕ :=
  Nat.card (properFixedPolycube n i)

end MetaMathlibExt
end
