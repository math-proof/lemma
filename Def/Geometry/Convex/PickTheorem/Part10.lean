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
import Theorem.Geometry.Convex.PickTheorem.Part10
/-!
# Pick's theorem for convex lattice polygons

This file proves Pick's area formula for full-dimensional convex hulls of finite sets of points in
the standard integer lattice. It also supplies the corresponding lattice-triangle theorem.
-/


namespace MetaMathlibExt

open Filter MeasureTheory

open scoped Pointwise

def pickSublattice (u v : Fin 2 → ℤ) : AddSubgroup (Fin 2 → ℤ) :=
  (pickIntMap u v).toAddMonoidHom.range

noncomputable def pickSublatticeBasis (u v : Fin 2 → ℤ) (h : pickDet u v ≠ 0) :
    Module.Basis (Fin 2) ℤ (pickSublattice u v) :=
  let g : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) := (pickIntMap u v).toAddMonoidHom
  let f : (Fin 2 → ℤ) →+ pickSublattice u v := g.rangeRestrict
  let e : (Fin 2 → ℤ) ≃+ pickSublattice u v := AddEquiv.ofBijective f ⟨by
    intro x y hxy
    exact pick_intMap_injective u v h (congrArg Subtype.val hxy), g.rangeRestrict_surjective⟩
  (Pi.basisFun ℤ (Fin 2)).map e.toIntLinearEquiv

end MetaMathlibExt
