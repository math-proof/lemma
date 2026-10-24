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

/-- Regular tetrahedron vertices (symmetric `±1` coordinates). -/
private def tetVert : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

/-- Three vertex differences spanning the tetrahedron. -/
private def tetD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![tetVert 1 - tetVert 0, tetVert 2 - tetVert 0, tetVert 3 - tetVert 0]
section Helpers
end Helpers
section Tetrahedron

/-- Tetrahedron edge endpoints (all six unordered vertex pairs). -/
private def tetEdge : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Tetrahedron faces: face `f` omits vertex `f`. -/
private def tetFace : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

/-- Face-local separating normals (coordinate directions). -/
private def tetFaceSepN : Fin 4 → Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![![!₂[(1 : ℝ), 0, 0], !₂[0, 1, 0], !₂[0, 0, 1]],
    ![!₂[(1 : ℝ), 0, 0], !₂[0, 0, -1], !₂[0, -1, 0]],
    ![!₂[(0 : ℝ), 1, 0], !₂[0, 0, -1], !₂[-1, 0, 0]],
    ![!₂[(0 : ℝ), 0, 1], !₂[0, -1, 0], !₂[-1, 0, 0]]]

/-- Supporting-plane normals (negated vertices). -/
private def tetSuppN : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(-1 : ℝ), -1, -1], !₂[-1, 1, 1], !₂[1, -1, 1], !₂[1, 1, -1]]

/-- For each vertex, a face containing it. -/
private def tetVertFace : Fin 4 → Fin 4 := ![1, 2, 3, 0]

/-- Index witnessing the vertex-face membership above. -/
private def tetVertFaceIdx : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The two faces containing each tetrahedron edge. -/
private def tetEdgeFaces : Fin 6 → Fin 4 × Fin 4 :=
  ![(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)]

/-- The three faces containing each tetrahedron vertex. -/
private def tetVertFaces : Fin 4 → Fin 4 × Fin 4 × Fin 4 :=
  ![(1, 2, 3), (0, 2, 3), (0, 1, 3), (0, 1, 2)]

/-- Tetrahedron halfspaces (H-representation). -/
private def tetHalf (f : Fin 4) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (tetSuppN f) x ≤ 1}

/-- Tetrahedron barycentric weights from coordinates. -/
private noncomputable def tetW (x : EuclideanSpace ℝ (Fin 3)) : Fin 4 → ℝ :=
  ![(x 0 + x 1 + x 2 + 1) / 4, (x 0 - x 1 - x 2 + 1) / 4,
    (-x 0 + x 1 - x 2 + 1) / 4, (-x 0 - x 1 + x 2 + 1) / 4]
end Tetrahedron
section Cube

/-- Cube vertices (all `±1` corners). -/
private def cubeVert : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, 1, -1], !₂[1, -1, 1], !₂[1, -1, -1],
    !₂[(-1 : ℝ), 1, 1], !₂[-1, 1, -1], !₂[-1, -1, 1], !₂[-1, -1, -1]]

/-- Cube edge endpoints (pairs differing in one coordinate). -/
private def cubeEdge : Fin 12 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3),
    (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)]

/-- Cube faces as cyclic vertex lists. -/
private def cubeFace : Fin 6 → Fin 4 → Fin 8 :=
  ![![0, 1, 3, 2], ![4, 5, 7, 6], ![0, 1, 5, 4],
    ![2, 3, 7, 6], ![0, 2, 6, 4], ![1, 3, 7, 5]]

/-- Face-local separating normals (in-plane diagonals). -/
private def cubeFaceSepN : Fin 6 → Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![![!₂[(0 : ℝ), 1, 1], !₂[0, 1, -1], !₂[0, -1, -1], !₂[0, -1, 1]],
    ![!₂[(0 : ℝ), 1, 1], !₂[0, 1, -1], !₂[0, -1, -1], !₂[0, -1, 1]],
    ![!₂[(1 : ℝ), 0, 1], !₂[1, 0, -1], !₂[-1, 0, -1], !₂[-1, 0, 1]],
    ![!₂[(1 : ℝ), 0, 1], !₂[1, 0, -1], !₂[-1, 0, -1], !₂[-1, 0, 1]],
    ![!₂[(1 : ℝ), 1, 0], !₂[1, -1, 0], !₂[-1, -1, 0], !₂[-1, 1, 0]],
    ![!₂[(1 : ℝ), 1, 0], !₂[1, -1, 0], !₂[-1, -1, 0], !₂[-1, 1, 0]]]

/-- Supporting-plane normals (coordinate directions). -/
private def cubeSuppN : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0],
    !₂[(0 : ℝ), -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- For each vertex, a face containing it. -/
private def cubeVertFace : Fin 8 → Fin 6 := ![0, 0, 0, 0, 1, 1, 1, 1]

/-- Index witnessing the vertex-face membership above. -/
private def cubeVertFaceIdx : Fin 8 → Fin 4 := ![0, 1, 3, 2, 0, 1, 3, 2]

/-- The two faces containing each cube edge. -/
private def cubeEdgeFaces : Fin 12 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 4), (2, 4), (0, 5), (2, 5), (0, 3),
    (3, 4), (3, 5), (1, 2), (1, 4), (1, 5), (1, 3)]

/-- The three faces containing each cube vertex. -/
private def cubeVertFaces : Fin 8 → Fin 6 × Fin 6 × Fin 6 :=
  ![(0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5),
    (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5)]

/-- Three vertex differences spanning the cube. -/
private def cubeD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![cubeVert 1 - cubeVert 0, cubeVert 2 - cubeVert 0, cubeVert 4 - cubeVert 0]

/-- Face-plane basis vectors (first). -/
private def cubeFaceB1 : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 1, 0], !₂[0, 1, 0], !₂[1, 0, 0],
    !₂[(1 : ℝ), 0, 0], !₂[1, 0, 0], !₂[1, 0, 0]]

/-- Face-plane basis vectors (second). -/
private def cubeFaceB2 : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 0, 1], !₂[0, 0, 1], !₂[0, 0, 1],
    !₂[(0 : ℝ), 0, 1], !₂[0, 1, 0], !₂[0, 1, 0]]

/-- Cube H-representation halfspaces. -/
private def cubeHalf (f : Fin 6) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (cubeSuppN f) x ≤ 1}

/-- Cube barycentric weights (trilinear interpolation). -/
private noncomputable def cubeW (x : EuclideanSpace ℝ (Fin 3)) : Fin 8 → ℝ :=
  ![(1 + x 0) * (1 + x 1) * (1 + x 2) / 8, (1 + x 0) * (1 + x 1) * (1 - x 2) / 8,
    (1 + x 0) * (1 - x 1) * (1 + x 2) / 8, (1 + x 0) * (1 - x 1) * (1 - x 2) / 8,
    (1 - x 0) * (1 + x 1) * (1 + x 2) / 8, (1 - x 0) * (1 + x 1) * (1 - x 2) / 8,
    (1 - x 0) * (1 - x 1) * (1 + x 2) / 8, (1 - x 0) * (1 - x 1) * (1 - x 2) / 8]
end Cube
section Octahedron

/-- Octahedron vertices, the positive and negative coordinate vectors. -/
private def octVert : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0],
    !₂[(0 : ℝ), -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- Octahedron edge endpoints, all non-antipodal pairs of vertices. -/
private def octEdge : Fin 12 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3),
    (1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]

/-- Octahedron faces as cyclic vertex lists. -/
private def octFace : Fin 8 → Fin 3 → Fin 6 :=
  ![![0, 2, 4], ![0, 5, 2], ![0, 4, 3], ![0, 3, 5],
    ![1, 4, 2], ![1, 2, 5], ![1, 3, 4], ![1, 5, 3]]

/-- Supporting-plane normals for the octahedron faces. -/
private def octSuppN : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, 1, -1], !₂[1, -1, 1], !₂[1, -1, -1],
    !₂[(-1 : ℝ), 1, 1], !₂[-1, 1, -1], !₂[-1, -1, 1], !₂[-1, -1, -1]]

/-- For each octahedron vertex, a face containing it. -/
private def octVertFace : Fin 6 → Fin 8 := ![0, 4, 0, 2, 0, 1]

/-- Index witnessing the assigned octahedron vertex-face membership. -/
private def octVertFaceIdx : Fin 6 → Fin 3 := ![0, 0, 1, 2, 2, 1]

/-- The two faces containing each octahedron edge. -/
private def octEdgeFaces : Fin 12 → Fin 8 × Fin 8 :=
  ![(0, 1), (2, 3), (0, 2), (1, 3), (4, 5), (6, 7),
    (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)]

/-- The four faces containing each octahedron vertex. -/
private def octVertFaces : Fin 6 → Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0, 1, 2, 3), (4, 5, 6, 7), (0, 1, 4, 5),
    (2, 3, 6, 7), (0, 2, 4, 6), (1, 3, 5, 7)]

/-- Three vertex differences spanning the octahedron. -/
private def octD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![octVert 0 - octVert 1, octVert 2 - octVert 3, octVert 4 - octVert 5]

/-- The halfspace determined by an octahedron face. -/
private def octHalf (f : Fin 8) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (octSuppN f) x ≤ 1}

/-- Barycentric weights for the cross-polytope H-representation. -/
private noncomputable def octW (x : EuclideanSpace ℝ (Fin 3)) : Fin 6 → ℝ :=
  ![(1 + x 0 - |x 1| - |x 2|) / 2,
    (1 - x 0 - |x 1| - |x 2|) / 2,
    (x 1 + |x 1|) / 2, (-x 1 + |x 1|) / 2,
    (x 2 + |x 2|) / 2, (-x 2 + |x 2|) / 2]

/-- Face-local barycentric weights for the octahedron. -/
private def octFaceW (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ :=
  ![![x 0, x 1, x 2], ![x 0, -x 2, x 1],
    ![x 0, x 2, -x 1], ![x 0, -x 1, -x 2],
    ![-x 0, x 2, x 1], ![-x 0, x 1, -x 2],
    ![-x 0, -x 1, x 2], ![-x 0, -x 2, -x 1]] f
end Octahedron
section GoldenSolids

private noncomputable def gold : ℝ := Real.goldenRatio

local notation "φ" => gold

/-- Icosahedron vertices in the standard golden-ratio coordinates. -/
private noncomputable def icoVert : Fin 12 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 1, φ], !₂[0, 1, -φ], !₂[0, -1, φ], !₂[0, -1, -φ],
    !₂[(1 : ℝ), φ, 0], !₂[1, -φ, 0], !₂[-1, φ, 0], !₂[-1, -φ, 0],
    !₂[(φ : ℝ), 0, 1], !₂[φ, 0, -1], !₂[-φ, 0, 1], !₂[-φ, 0, -1]]

/-- Icosahedron edge endpoints. -/
private def icoEdge : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 2), (0, 4), (0, 6), (0, 8), (0, 10),
    (1, 3), (1, 4), (1, 6), (1, 9), (1, 11),
    (2, 5), (2, 7), (2, 8), (2, 10),
    (3, 5), (3, 7), (3, 9), (3, 11),
    (4, 6), (4, 8), (4, 9), (5, 7), (5, 8), (5, 9),
    (6, 10), (6, 11), (7, 10), (7, 11), (8, 9), (10, 11)]

/-- Icosahedron faces as cyclic vertex lists. -/
private def icoFace : Fin 20 → Fin 3 → Fin 12 :=
  ![![0, 2, 8], ![0, 2, 10], ![0, 4, 6], ![0, 4, 8], ![0, 6, 10],
    ![1, 3, 9], ![1, 3, 11], ![1, 4, 6], ![1, 4, 9], ![1, 6, 11],
    ![2, 5, 7], ![2, 5, 8], ![2, 7, 10], ![3, 5, 7], ![3, 5, 9],
    ![3, 7, 11], ![4, 8, 9], ![5, 8, 9], ![6, 10, 11], ![7, 10, 11]]

/-- Dodecahedron vertices, scaled by `φ` so their edge length is two.
The order is dual to `icoFace`. -/
private noncomputable def dodVert : Fin 20 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, φ ^ 2], !₂[-1, 0, φ ^ 2], !₂[0, φ ^ 2, 1],
    !₂[(φ : ℝ), φ, φ], !₂[-φ, φ, φ], !₂[1, 0, -(φ ^ 2)],
    !₂[(-1 : ℝ), 0, -(φ ^ 2)], !₂[0, φ ^ 2, -1], !₂[φ, φ, -φ],
    !₂[(-φ : ℝ), φ, -φ], !₂[0, -(φ ^ 2), 1], !₂[φ, -φ, φ],
    !₂[(-φ : ℝ), -φ, φ], !₂[0, -(φ ^ 2), -1], !₂[φ, -φ, -φ],
    !₂[(-φ : ℝ), -φ, -φ], !₂[φ ^ 2, 1, 0], !₂[φ ^ 2, -1, 0],
    !₂[-(φ ^ 2), 1, 0], !₂[-(φ ^ 2), -1, 0]]

/-- Dodecahedron edge endpoints. -/
private def dodEdge : Fin 30 → Fin 20 × Fin 20 :=
  ![(0, 1), (0, 3), (0, 11), (1, 4), (1, 12),
    (2, 3), (2, 4), (2, 7), (3, 16), (4, 18),
    (5, 6), (5, 8), (5, 14), (6, 9), (6, 15),
    (7, 8), (7, 9), (8, 16), (9, 18),
    (10, 11), (10, 12), (10, 13), (11, 17), (12, 19),
    (13, 14), (13, 15), (14, 17), (15, 19), (16, 17), (18, 19)]

/-- Dodecahedron faces as cyclic vertex lists. -/
private def dodFace : Fin 12 → Fin 5 → Fin 20 :=
  ![![0, 1, 4, 2, 3], ![5, 6, 9, 7, 8], ![0, 1, 12, 10, 11],
    ![5, 6, 15, 13, 14], ![2, 3, 16, 8, 7], ![10, 11, 17, 14, 13],
    ![2, 4, 18, 9, 7], ![10, 12, 19, 15, 13], ![0, 3, 16, 17, 11],
    ![5, 8, 16, 17, 14], ![1, 4, 18, 19, 12], ![6, 9, 18, 19, 15]]

section Icosahedron

/-- The common support value for the dual golden-ratio coordinate systems. -/
private noncomputable def goldC : ℝ := 2 * φ + 1

/-- Supporting-plane normals for the icosahedron faces. -/
private noncomputable def icoSuppN : Fin 20 → EuclideanSpace ℝ (Fin 3) := dodVert

/-- For each icosahedron vertex, a face containing it. -/
private def icoVertFace : Fin 12 → Fin 20 :=
  ![0, 5, 0, 5, 2, 10, 2, 10, 0, 5, 1, 6]

/-- Index witnessing the assigned icosahedron vertex-face membership. -/
private def icoVertFaceIdx : Fin 12 → Fin 3 :=
  ![0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2]

/-- The two faces containing each icosahedron edge. -/
private def icoEdgeFaces : Fin 30 → Fin 20 × Fin 20 :=
  ![(0, 1), (2, 3), (2, 4), (0, 3), (1, 4),
    (5, 6), (7, 8), (7, 9), (5, 8), (6, 9),
    (10, 11), (10, 12), (0, 11), (1, 12),
    (13, 14), (13, 15), (5, 14), (6, 15),
    (2, 7), (3, 16), (8, 16), (10, 13), (11, 17), (14, 17),
    (4, 18), (9, 18), (12, 19), (15, 19), (16, 17), (18, 19)]

/-- The five faces containing each icosahedron vertex. -/
private def icoVertFaces : Fin 12 → Fin 5 → Fin 20 :=
  ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![0, 1, 10, 11, 12],
    ![5, 6, 13, 14, 15], ![2, 3, 7, 8, 16], ![10, 11, 13, 14, 17],
    ![2, 4, 7, 9, 18], ![10, 12, 13, 15, 19], ![0, 3, 11, 16, 17],
    ![5, 8, 14, 16, 17], ![1, 4, 12, 18, 19], ![6, 9, 15, 18, 19]]

/-- Three vertex differences spanning the icosahedron. -/
private noncomputable def icoD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![icoVert 0 - icoVert 1, icoVert 4 - icoVert 5,
    icoVert 8 - icoVert 10]

/-- The halfspace determined by an icosahedron face. -/
private def icoHalf (f : Fin 20) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (icoSuppN f) x ≤ goldC}

/-- Across each edge opposite a local face vertex, the adjacent face. -/
private def icoFaceOpp : Fin 20 → Fin 3 → Fin 20 :=
  ![![11, 3, 1], ![12, 4, 0], ![7, 4, 3], ![16, 0, 2],
    ![18, 1, 2], ![14, 8, 6], ![15, 9, 5], ![2, 9, 8],
    ![16, 5, 7], ![18, 6, 7], ![13, 12, 11], ![17, 0, 10],
    ![19, 1, 10], ![10, 15, 14], ![17, 5, 13], ![19, 6, 13],
    ![17, 8, 3], ![16, 14, 11], ![19, 9, 4], ![18, 15, 12]]

/-- Face-local barycentric weights for the icosahedron. -/
private noncomputable def icoFaceW (f : Fin 20)
    (x : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) : ℝ :=
  (inner (𝕜 := ℝ) (icoVert (icoFace f i)) x - φ) / 2
end Icosahedron
section Dodecahedron

/-- Supporting-plane normals for the dodecahedron faces. -/
private noncomputable def dodSuppN : Fin 12 → EuclideanSpace ℝ (Fin 3) :=
  icoVert

/-- For each dodecahedron vertex, a face containing it. -/
private def dodVertFace : Fin 20 → Fin 12 :=
  ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 4, 5, 6, 7]

/-- Index witnessing the assigned dodecahedron vertex-face membership. -/
private def dodVertFaceIdx : Fin 20 → Fin 5 :=
  ![0, 1, 3, 4, 2, 0, 1, 3, 4, 2, 3, 4, 2, 3, 4, 2, 2, 2, 2, 2]

/-- The two faces containing each dodecahedron edge. -/
private def dodEdgeFaces : Fin 30 → Fin 12 × Fin 12 :=
  ![(0, 2), (0, 8), (2, 8), (0, 10), (2, 10),
    (0, 4), (0, 6), (4, 6), (4, 8), (6, 10),
    (1, 3), (1, 9), (3, 9), (1, 11), (3, 11),
    (1, 4), (1, 6), (4, 9), (6, 11), (2, 5),
    (2, 7), (5, 7), (5, 8), (7, 10), (3, 5),
    (3, 7), (5, 9), (7, 11), (8, 9), (10, 11)]

/-- The three faces containing each dodecahedron vertex. -/
private def dodVertFaces : Fin 20 → Fin 3 → Fin 12 := icoFace

/-- Three vertex differences spanning the dodecahedron. -/
private noncomputable def dodD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![dodVert 0 - dodVert 1, dodVert 16 - dodVert 17,
    dodVert 2 - dodVert 7]

/-- The halfspace determined by a dodecahedron face. -/
private def dodHalf (f : Fin 12) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (dodSuppN f) x ≤ goldC}
end Dodecahedron
end GoldenSolids
end
end MetaMathlibExt
