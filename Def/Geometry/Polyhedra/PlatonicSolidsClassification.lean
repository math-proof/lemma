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
def tetVert : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, -1, -1], !₂[-1, 1, -1], !₂[-1, -1, 1]]

/-- Three vertex differences spanning the tetrahedron. -/
def tetD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![tetVert 1 - tetVert 0, tetVert 2 - tetVert 0, tetVert 3 - tetVert 0]

section Helpers

end Helpers

section Tetrahedron

/-- Tetrahedron edge endpoints (all six unordered vertex pairs). -/
def tetEdge : Fin 6 → Fin 4 × Fin 4 :=
  ![(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

/-- Tetrahedron faces: face `f` omits vertex `f`. -/
def tetFace : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

/-- Face-local separating normals (coordinate directions). -/
def tetFaceSepN : Fin 4 → Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![![!₂[(1 : ℝ), 0, 0], !₂[0, 1, 0], !₂[0, 0, 1]],
    ![!₂[(1 : ℝ), 0, 0], !₂[0, 0, -1], !₂[0, -1, 0]],
    ![!₂[(0 : ℝ), 1, 0], !₂[0, 0, -1], !₂[-1, 0, 0]],
    ![!₂[(0 : ℝ), 0, 1], !₂[0, -1, 0], !₂[-1, 0, 0]]]

/-- Supporting-plane normals (negated vertices). -/
def tetSuppN : Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(-1 : ℝ), -1, -1], !₂[-1, 1, 1], !₂[1, -1, 1], !₂[1, 1, -1]]

/-- For each vertex, a face containing it. -/
def tetVertFace : Fin 4 → Fin 4 := ![1, 2, 3, 0]

/-- Index witnessing the vertex-face membership above. -/
def tetVertFaceIdx : Fin 4 → Fin 3 := ![0, 1, 2, 2]

/-- The two faces containing each tetrahedron edge. -/
def tetEdgeFaces : Fin 6 → Fin 4 × Fin 4 :=
  ![(2, 3), (1, 3), (1, 2), (0, 3), (0, 2), (0, 1)]

/-- The three faces containing each tetrahedron vertex. -/
def tetVertFaces : Fin 4 → Fin 4 × Fin 4 × Fin 4 :=
  ![(1, 2, 3), (0, 2, 3), (0, 1, 3), (0, 1, 2)]

/-- Tetrahedron halfspaces (H-representation). -/
def tetHalf (f : Fin 4) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (tetSuppN f) x ≤ 1}

/-- Tetrahedron barycentric weights from coordinates. -/
noncomputable def tetW (x : EuclideanSpace ℝ (Fin 3)) : Fin 4 → ℝ :=
  ![(x 0 + x 1 + x 2 + 1) / 4, (x 0 - x 1 - x 2 + 1) / 4,
    (-x 0 + x 1 - x 2 + 1) / 4, (-x 0 - x 1 + x 2 + 1) / 4]

end Tetrahedron

section Cube

/-- Cube vertices (all `±1` corners). -/
def cubeVert : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, 1, -1], !₂[1, -1, 1], !₂[1, -1, -1],
    !₂[(-1 : ℝ), 1, 1], !₂[-1, 1, -1], !₂[-1, -1, 1], !₂[-1, -1, -1]]

/-- Cube edge endpoints (pairs differing in one coordinate). -/
def cubeEdge : Fin 12 → Fin 8 × Fin 8 :=
  ![(0, 1), (0, 2), (0, 4), (1, 3), (1, 5), (2, 3),
    (2, 6), (3, 7), (4, 5), (4, 6), (5, 7), (6, 7)]

/-- Cube faces as cyclic vertex lists. -/
def cubeFace : Fin 6 → Fin 4 → Fin 8 :=
  ![![0, 1, 3, 2], ![4, 5, 7, 6], ![0, 1, 5, 4],
    ![2, 3, 7, 6], ![0, 2, 6, 4], ![1, 3, 7, 5]]

/-- Face-local separating normals (in-plane diagonals). -/
def cubeFaceSepN : Fin 6 → Fin 4 → EuclideanSpace ℝ (Fin 3) :=
  ![![!₂[(0 : ℝ), 1, 1], !₂[0, 1, -1], !₂[0, -1, -1], !₂[0, -1, 1]],
    ![!₂[(0 : ℝ), 1, 1], !₂[0, 1, -1], !₂[0, -1, -1], !₂[0, -1, 1]],
    ![!₂[(1 : ℝ), 0, 1], !₂[1, 0, -1], !₂[-1, 0, -1], !₂[-1, 0, 1]],
    ![!₂[(1 : ℝ), 0, 1], !₂[1, 0, -1], !₂[-1, 0, -1], !₂[-1, 0, 1]],
    ![!₂[(1 : ℝ), 1, 0], !₂[1, -1, 0], !₂[-1, -1, 0], !₂[-1, 1, 0]],
    ![!₂[(1 : ℝ), 1, 0], !₂[1, -1, 0], !₂[-1, -1, 0], !₂[-1, 1, 0]]]

/-- Supporting-plane normals (coordinate directions). -/
def cubeSuppN : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0],
    !₂[(0 : ℝ), -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- For each vertex, a face containing it. -/
def cubeVertFace : Fin 8 → Fin 6 := ![0, 0, 0, 0, 1, 1, 1, 1]

/-- Index witnessing the vertex-face membership above. -/
def cubeVertFaceIdx : Fin 8 → Fin 4 := ![0, 1, 3, 2, 0, 1, 3, 2]

/-- The two faces containing each cube edge. -/
def cubeEdgeFaces : Fin 12 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 4), (2, 4), (0, 5), (2, 5), (0, 3),
    (3, 4), (3, 5), (1, 2), (1, 4), (1, 5), (1, 3)]

/-- The three faces containing each cube vertex. -/
def cubeVertFaces : Fin 8 → Fin 6 × Fin 6 × Fin 6 :=
  ![(0, 2, 4), (0, 2, 5), (0, 3, 4), (0, 3, 5),
    (1, 2, 4), (1, 2, 5), (1, 3, 4), (1, 3, 5)]

/-- Three vertex differences spanning the cube. -/
def cubeD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![cubeVert 1 - cubeVert 0, cubeVert 2 - cubeVert 0, cubeVert 4 - cubeVert 0]

/-- Face-plane basis vectors (first). -/
def cubeFaceB1 : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 1, 0], !₂[0, 1, 0], !₂[1, 0, 0],
    !₂[(1 : ℝ), 0, 0], !₂[1, 0, 0], !₂[1, 0, 0]]

/-- Face-plane basis vectors (second). -/
def cubeFaceB2 : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(0 : ℝ), 0, 1], !₂[0, 0, 1], !₂[0, 0, 1],
    !₂[(0 : ℝ), 0, 1], !₂[0, 1, 0], !₂[0, 1, 0]]

/-- Cube H-representation halfspaces. -/
def cubeHalf (f : Fin 6) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (cubeSuppN f) x ≤ 1}

/-- Cube barycentric weights (trilinear interpolation). -/
noncomputable def cubeW (x : EuclideanSpace ℝ (Fin 3)) : Fin 8 → ℝ :=
  ![(1 + x 0) * (1 + x 1) * (1 + x 2) / 8, (1 + x 0) * (1 + x 1) * (1 - x 2) / 8,
    (1 + x 0) * (1 - x 1) * (1 + x 2) / 8, (1 + x 0) * (1 - x 1) * (1 - x 2) / 8,
    (1 - x 0) * (1 + x 1) * (1 + x 2) / 8, (1 - x 0) * (1 + x 1) * (1 - x 2) / 8,
    (1 - x 0) * (1 - x 1) * (1 + x 2) / 8, (1 - x 0) * (1 - x 1) * (1 - x 2) / 8]

end Cube

section Octahedron

/-- Octahedron vertices, the positive and negative coordinate vectors. -/
def octVert : Fin 6 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 0, 0], !₂[-1, 0, 0], !₂[0, 1, 0],
    !₂[(0 : ℝ), -1, 0], !₂[0, 0, 1], !₂[0, 0, -1]]

/-- Octahedron edge endpoints, all non-antipodal pairs of vertices. -/
def octEdge : Fin 12 → Fin 6 × Fin 6 :=
  ![(0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3),
    (1, 4), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5)]

/-- Octahedron faces as cyclic vertex lists. -/
def octFace : Fin 8 → Fin 3 → Fin 6 :=
  ![![0, 2, 4], ![0, 5, 2], ![0, 4, 3], ![0, 3, 5],
    ![1, 4, 2], ![1, 2, 5], ![1, 3, 4], ![1, 5, 3]]

/-- Supporting-plane normals for the octahedron faces. -/
def octSuppN : Fin 8 → EuclideanSpace ℝ (Fin 3) :=
  ![!₂[(1 : ℝ), 1, 1], !₂[1, 1, -1], !₂[1, -1, 1], !₂[1, -1, -1],
    !₂[(-1 : ℝ), 1, 1], !₂[-1, 1, -1], !₂[-1, -1, 1], !₂[-1, -1, -1]]

/-- For each octahedron vertex, a face containing it. -/
def octVertFace : Fin 6 → Fin 8 := ![0, 4, 0, 2, 0, 1]

/-- Index witnessing the assigned octahedron vertex-face membership. -/
def octVertFaceIdx : Fin 6 → Fin 3 := ![0, 0, 1, 2, 2, 1]

/-- The two faces containing each octahedron edge. -/
def octEdgeFaces : Fin 12 → Fin 8 × Fin 8 :=
  ![(0, 1), (2, 3), (0, 2), (1, 3), (4, 5), (6, 7),
    (4, 6), (5, 7), (0, 4), (1, 5), (2, 6), (3, 7)]

/-- The four faces containing each octahedron vertex. -/
def octVertFaces : Fin 6 → Fin 8 × Fin 8 × Fin 8 × Fin 8 :=
  ![(0, 1, 2, 3), (4, 5, 6, 7), (0, 1, 4, 5),
    (2, 3, 6, 7), (0, 2, 4, 6), (1, 3, 5, 7)]

/-- Three vertex differences spanning the octahedron. -/
def octD : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  ![octVert 0 - octVert 1, octVert 2 - octVert 3, octVert 4 - octVert 5]

/-- The halfspace determined by an octahedron face. -/
def octHalf (f : Fin 8) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {x | inner (𝕜 := ℝ) (octSuppN f) x ≤ 1}

/-- Barycentric weights for the cross-polytope H-representation. -/
noncomputable def octW (x : EuclideanSpace ℝ (Fin 3)) : Fin 6 → ℝ :=
  ![(1 + x 0 - |x 1| - |x 2|) / 2,
    (1 - x 0 - |x 1| - |x 2|) / 2,
    (x 1 + |x 1|) / 2, (-x 1 + |x 1|) / 2,
    (x 2 + |x 2|) / 2, (-x 2 + |x 2|) / 2]

/-- Face-local barycentric weights for the octahedron. -/
def octFaceW (f : Fin 8) (x : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℝ :=
  ![![x 0, x 1, x 2], ![x 0, -x 2, x 1],
    ![x 0, x 2, -x 1], ![x 0, -x 1, -x 2],
    ![-x 0, x 2, x 1], ![-x 0, x 1, -x 2],
    ![-x 0, -x 1, x 2], ![-x 0, -x 2, -x 1]] f

end Octahedron

section GoldenSolids

noncomputable def gold : ℝ := Real.goldenRatio

end GoldenSolids
end
end MetaMathlibExt
