module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.Convex.Independent
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Analysis.Convex.Radon
public import Mathlib.Analysis.Convex.Strict.Extreme
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Topology.Instances.ZMultiples
public import Theorem.Geometry.Convex.PickTheorem.Part13


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Convex/PickTheorem.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/
namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

noncomputable def pickQuotientFundamentalEquiv (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    ((Fin 2 → ℤ) ⧸ pickSublattice u v) ≃ pickFundamentalLatticePoints u v h :=
  Equiv.ofBijective (pickQuotientToFundamental u v h)
    (pick_quotientToFundamental_bijective u v h)

end MetaMathlibExt
