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
import Theorem.Geometry.Convex.PickTheorem.Part12
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

noncomputable def pickFundamentalLatticePoints (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) : Set (Fin 2 → ℤ) :=
  {z | pickCast z ∈ ZSpan.fundamentalDomain (pickBasis u v h)}

noncomputable def pickQuotientToFundamental (u v : Fin 2 → ℤ)
    (h : pickDet u v ≠ 0) :
    ((Fin 2 → ℤ) ⧸ pickSublattice u v) → pickFundamentalLatticePoints u v h := fun q ↦
  Quotient.liftOn q
    (fun z ↦ ⟨pickFractInt u v z h, pick_fractInt_mem_fundamentalDomain u v z h⟩)
    (fun _ _ hrel ↦ Subtype.ext (pick_fractInt_eq_of_rel u v h hrel))

end MetaMathlibExt
