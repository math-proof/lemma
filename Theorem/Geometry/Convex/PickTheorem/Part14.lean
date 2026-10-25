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
import Def.Geometry.Convex.PickTheorem.Part13
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

theorem pick_fundamentalLatticePoints_ncard (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    (pickFundamentalLatticePoints u v h).ncard = (pickDet u v).natAbs := by
  calc
    (pickFundamentalLatticePoints u v h).ncard =
        Nat.card (pickFundamentalLatticePoints u v h) := by
      rw [← Set.ncard_coe, Set.ncard_univ]
    _ = Nat.card ((Fin 2 → ℤ) ⧸ pickSublattice u v) :=
      (Nat.card_congr (pickQuotientFundamentalEquiv u v h)).symm
    _ = (pickSublattice u v).index := (pickSublattice u v).index_eq_card.symm
    _ = (pickDet u v).natAbs := pick_sublattice_index u v h

end MetaMathlibExt
