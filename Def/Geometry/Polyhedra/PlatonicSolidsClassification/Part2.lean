/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Polyhedra/PlatonicSolidsClassification.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Notation.Geometry.Polyhedra.PlatonicSolidsClassification
/-!
# Classification of the Platonic solids

This file classifies the Platonic solids up to their count tuple `(p, q, V, E, F)` and proves that
each of the five tuples is realized. Euler's formula and the two incidence-count equations imply
`1 / p + 1 / q > 1 / 2`, leaving only the five classical count tuples; explicit Euclidean
coordinates realize every tuple. Classification up to combinatorial equivalence or Euclidean
congruence is not proved here.
-/


namespace MetaMathlibExt

section

section GoldenSolids

local notation "φ" => gold

/-- Icosahedron vertices in the standard golden-ratio coordinates. -/
noncomputable def icoVert : Fin 12 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 1, φ], !₂[0, 1, -φ], !₂[0, -1, φ], !₂[0, -1, -φ],
    !₂[(1 : ℝ), φ, 0], !₂[1, -φ, 0], !₂[-1, φ, 0], !₂[-1, -φ, 0],
    !₂[(φ : ℝ), 0, 1], !₂[φ, 0, -1], !₂[-φ, 0, 1], !₂[-φ, 0, -1]]

/-- Icosahedron edge endpoints. -/
def icoEdge : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 2), (0, 4), (0, 6), (0, 8), (0, 10),
    (1, 3), (1, 4), (1, 6), (1, 9), (1, 11),
    (2, 5), (2, 7), (2, 8), (2, 10),
    (3, 5), (3, 7), (3, 9), (3, 11),
    (4, 6), (4, 8), (4, 9), (5, 7), (5, 8), (5, 9),
    (6, 10), (6, 11), (7, 10), (7, 11), (8, 9), (10, 11)]

/-- Icosahedron faces as cyclic vertex lists. -/
def icoFace : Fin 20 → Fin 3 → Fin 12 :=
  ![![0, 2, 8], ![0, 2, 10], ![0, 4, 6], ![0, 4, 8], ![0, 6, 10],
    ![1, 3, 9], ![1, 3, 11], ![1, 4, 6], ![1, 4, 9], ![1, 6, 11],
    ![2, 5, 7], ![2, 5, 8], ![2, 7, 10], ![3, 5, 7], ![3, 5, 9],
    ![3, 7, 11], ![4, 8, 9], ![5, 8, 9], ![6, 10, 11], ![7, 10, 11]]

/-- Dodecahedron vertices, scaled by `φ` so their edge length is two.
The order is dual to `icoFace`. -/
noncomputable def dodVert : Fin 20 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, φ ^ 2], !₂[-1, 0, φ ^ 2], !₂[0, φ ^ 2, 1],
    !₂[(φ : ℝ), φ, φ], !₂[-φ, φ, φ], !₂[1, 0, -(φ ^ 2)],
    !₂[(-1 : ℝ), 0, -(φ ^ 2)], !₂[0, φ ^ 2, -1], !₂[φ, φ, -φ],
    !₂[(-φ : ℝ), φ, -φ], !₂[0, -(φ ^ 2), 1], !₂[φ, -φ, φ],
    !₂[(-φ : ℝ), -φ, φ], !₂[0, -(φ ^ 2), -1], !₂[φ, -φ, -φ],
    !₂[(-φ : ℝ), -φ, -φ], !₂[φ ^ 2, 1, 0], !₂[φ ^ 2, -1, 0],
    !₂[-(φ ^ 2), 1, 0], !₂[-(φ ^ 2), -1, 0]]

/-- Dodecahedron edge endpoints. -/
def dodEdge : Fin 30 → Fin 20 × Fin 20 :=
  ![(0, 1), (0, 3), (0, 11), (1, 4), (1, 12),
    (2, 3), (2, 4), (2, 7), (3, 16), (4, 18),
    (5, 6), (5, 8), (5, 14), (6, 9), (6, 15),
    (7, 8), (7, 9), (8, 16), (9, 18),
    (10, 11), (10, 12), (10, 13), (11, 17), (12, 19),
    (13, 14), (13, 15), (14, 17), (15, 19), (16, 17), (18, 19)]

/-- Dodecahedron faces as cyclic vertex lists. -/
def dodFace : Fin 12 → Fin 5 → Fin 20 :=
  ![![0, 1, 4, 2, 3], ![5, 6, 9, 7, 8], ![0, 1, 12, 10, 11],
    ![5, 6, 15, 13, 14], ![2, 3, 16, 8, 7], ![10, 11, 17, 14, 13],
    ![2, 4, 18, 9, 7], ![10, 12, 19, 15, 13], ![0, 3, 16, 17, 11],
    ![5, 8, 16, 17, 14], ![1, 4, 18, 19, 12], ![6, 9, 18, 19, 15]]

section Icosahedron

/-- The common support value for the dual golden-ratio coordinate systems. -/
noncomputable def goldC : ℝ := 2 * φ + 1

/-- Supporting-plane normals for the icosahedron faces. -/
noncomputable def icoSuppN : Fin 20 → EuclideanSpace ℝ (Fin 3) := dodVert

/-- For each icosahedron vertex, a face containing it. -/
def icoVertFace : Fin 12 → Fin 20 :=
  ![0, 5, 0, 5, 2, 10, 2, 10, 0, 5, 1, 6]

/-- Index witnessing the assigned icosahedron vertex-face membership. -/
def icoVertFaceIdx : Fin 12 → Fin 3 :=
  ![0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]

/-- The two faces containing each icosahedron edge. -/
def icoEdgeFaces : Fin 30 → Fin 20 × Fin 20 :=
  ![(0, 1), (2, 3), (2, 4), (0, 3), (1, 4),
    (5, 6), (7, 8), (7, 9), (5, 8), (6, 9),
    (10, 11), (10, 12), (0, 11), (1, 12),
    (13, 14), (13, 15), (5, 14), (6, 15),
    (2, 7), (3, 16), (8, 16), (10, 13), (11, 17), (14, 17),
    (4, 18), (9, 18), (12, 19), (15, 19), (16, 17), (18, 19)]

/-- The five faces containing each icosahedron vertex. -/
def icoVertFaces : Fin 12 → Fin 5 → Fin 20 :=
  ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![0, 1, 10, 11, 12],
    ![5, 6, 13, 14, 15], ![2, 3, 7, 8, 16], ![10, 11, 13, 14, 17],
    ![2, 4, 7, 9, 18], ![10, 12, 13, 15, 19], ![0, 3, 11, 16, 17],
    ![5, 8, 14, 16, 17], ![1, 4, 12, 18, 19], ![6, 9, 15, 18, 19]]

/-- Three vertex differences spanning the icosahedron. -/
noncomputable def icoD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![icoVert 0 - icoVert 1, icoVert 4 - icoVert 5,
    icoVert 8 - icoVert 10]

/-- The halfspace determined by an icosahedron face. -/
def icoHalf (f : Fin 20) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (icoSuppN f) x ≤ goldC}

/-- Across each edge opposite a local face vertex, the adjacent face. -/
def icoFaceOpp : Fin 20 → Fin 3 → Fin 20 :=
  ![![11, 3, 1], ![12, 4, 0], ![7, 4, 3], ![16, 0, 2],
    ![18, 1, 2], ![14, 8, 6], ![15, 9, 5], ![2, 9, 8],
    ![16, 5, 7], ![18, 6, 7], ![13, 12, 11], ![17, 0, 10],
    ![19, 1, 10], ![10, 15, 14], ![17, 5, 13], ![19, 6, 13],
    ![17, 8, 3], ![16, 14, 11], ![19, 9, 4], ![18, 15, 12]]

/-- Face-local barycentric weights for the icosahedron. -/
noncomputable def icoFaceW (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : ℝ :=
  (inner (𝕜 := ℝ) (icoVert (icoFace f i)) x - φ) / 2

end Icosahedron

section Dodecahedron

/-- Supporting-plane normals for the dodecahedron faces. -/
noncomputable def dodSuppN : Fin 12 → EuclideanSpace ℝ (Fin 3) :=
  icoVert

/-- For each dodecahedron vertex, a face containing it. -/
def dodVertFace : Fin 20 → Fin 12 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 6, 7]

/-- Index witnessing the assigned dodecahedron vertex-face membership. -/
def dodVertFaceIdx : Fin 20 → Fin 5 :=
  ![0, 1, 3, 4, 2, 0, 1, 3, 4, 2, 3, 4, 2, 3, 4, 2, 2, 2, 2, 2]

/-- The two faces containing each dodecahedron edge. -/
def dodEdgeFaces : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 2), (0, 8), (2, 8), (0, 10), (2, 10),
    (0, 4), (0, 6), (4, 6), (4, 8), (6, 10),
    (1, 3), (1, 9), (3, 9), (1, 11), (3, 11),
    (1, 4), (1, 6), (4, 9), (6, 11), (2, 5),
    (2, 7), (5, 7), (5, 8), (7, 10), (3, 5),
    (3, 7), (5, 9), (7, 11), (8, 9), (10, 11)]

/-- The three faces containing each dodecahedron vertex. -/
def dodVertFaces : Fin 20 → Fin 3 → Fin 12 := icoFace

/-- Three vertex differences spanning the dodecahedron. -/
noncomputable def dodD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![dodVert 0 - dodVert 1, dodVert 16 - dodVert 17,
    dodVert 2 - dodVert 7]

/-- The halfspace determined by a dodecahedron face. -/
def dodHalf (f : Fin 12) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (dodSuppN f) x ≤ goldC}

end Dodecahedron
end GoldenSolids
end
end MetaMathlibExt
