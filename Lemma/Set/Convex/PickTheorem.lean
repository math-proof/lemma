import Mathlib
import sympy.Basic
import sympy.atlas.Geometry.Convex.PickTheorem
open Filter MeasureTheory
open scoped Pointwise
open MetaMathlibExt


/--
[_root_.MeasureTheory.toReal_volume_convexHull_lattice_triangle](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma MeasureTheory_toReal_volume_convexHull_lattice_triangle_eq
  {u v : Fin 2 → ℤ}
-- given
  (h : u 0 * v 1 - u 1 * v 0 ≠ 0) :
-- imply
  (volume (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
    Set (Fin 2 → ℝ)))).toReal =
    (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
    interior (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
    Set (Fin 2 → ℝ)))} : ℝ) +
    (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
    frontier (convexHull ℝ ({0, (fun i ↦ (u i : ℝ)), (fun i ↦ (v i : ℝ))} :
    Set (Fin 2 → ℝ)))} : ℝ) / 2 - 1 := by
-- proof
  apply MeasureTheory.toReal_volume_convexHull_lattice_triangle u v h

/--
[pick_convex_lattice_polygon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean)
-/
@[path]
private lemma pick_convex_lattice_polygon_eq
  {vertices : Finset (Fin 2 → ℤ)}
-- given
  (hfull : (interior (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
-- imply
  (volume
    (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).toReal =
    (Set.ncard {z : Fin 2 → ℤ |
    (fun i => (z i : ℝ)) ∈
    interior
    (convexHull ℝ ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) +
    (Set.ncard {z : Fin 2 → ℤ |
    (fun i => (z i : ℝ)) ∈
    frontier
    (convexHull ℝ
    ((fun z i => (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))} : ℝ) / 2 - 1 := by
-- proof
  apply MetaMathlibExt.pick_convex_lattice_polygon vertices hfull


-- created on 2026-10-20
