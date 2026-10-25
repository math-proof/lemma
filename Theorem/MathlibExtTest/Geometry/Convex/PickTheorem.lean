/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Convex/PickTheorem.lean -/

import Theorem.Geometry.Convex.PickTheorem.Part18
import Lemma.Set.Convex.PickTheorem
import Mathlib.Tactic


namespace MathlibExtTest.Geometry.Convex.PickTheorem

open MeasureTheory

-- Apply the triangle theorem to a determinant-six integer basis.
example :
    (volume (convexHull ℝ
      ({0, (fun i ↦ ((![2, 0] : Fin 2 → ℤ) i : ℝ)),
        (fun i ↦ ((![1, 3] : Fin 2 → ℤ) i : ℝ))} : Set (Fin 2 → ℝ)))).toReal =
      (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
        interior (convexHull ℝ
          ({0, (fun i ↦ ((![2, 0] : Fin 2 → ℤ) i : ℝ)),
            (fun i ↦ ((![1, 3] : Fin 2 → ℤ) i : ℝ))} : Set (Fin 2 → ℝ)))} : ℝ) +
      (Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈
        frontier (convexHull ℝ
          ({0, (fun i ↦ ((![2, 0] : Fin 2 → ℤ) i : ℝ)),
            (fun i ↦ ((![1, 3] : Fin 2 → ℤ) i : ℝ))} : Set (Fin 2 → ℝ)))} : ℝ) / 2 - 1 := by
  apply MeasureTheory.toReal_volume_convexHull_lattice_triangle
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

-- Twice the area of every full-dimensional convex lattice polygon is integral.
example (vertices : Finset (Fin 2 → ℤ))
    (hfull : (interior (convexHull ℝ
      ((fun z i ↦ (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).Nonempty) :
    ∃ n : ℤ, 2 * (volume (convexHull ℝ
      ((fun z i ↦ (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ))))).toReal = (n : ℝ) := by
  let P := convexHull ℝ ((fun z i ↦ (z i : ℝ)) '' (vertices : Set (Fin 2 → ℤ)))
  let I := Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈ interior P}
  let B := Set.ncard {z : Fin 2 → ℤ | (fun i ↦ (z i : ℝ)) ∈ frontier P}
  have h := MetaMathlibExt.pick_convex_lattice_polygon vertices hfull
  change (volume P).toReal = (I : ℝ) + (B : ℝ) / 2 - 1 at h
  refine ⟨2 * (I : ℤ) + (B : ℤ) - 2, ?_⟩
  rw [h]
  push_cast
  ring

end MathlibExtTest.Geometry.Convex.PickTheorem
