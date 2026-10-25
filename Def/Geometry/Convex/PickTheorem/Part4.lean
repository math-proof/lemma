/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Analysis.Convex.Between
import Mathlib.Analysis.Convex.Independent
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.Convex.Strict.Extreme
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.ZMultiples
import Theorem.Geometry.Convex.PickTheorem.Part4
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

noncomputable def pickAffineBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    AffineBasis (Fin 3) ℝ (Fin 2 → ℝ) :=
  let t : Affine.Simplex ℝ (Fin 2 → ℝ) 2 :=
    ⟨pickTrianglePoints u v h, pick_trianglePoints_affineIndependent u v h⟩
  AffineBasis.mk (pickTrianglePoints u v h) (pick_trianglePoints_affineIndependent u v h)
    (t.affineSpan_eq_top (by simp))

end MetaMathlibExt
