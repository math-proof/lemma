/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.SetTheory.Cardinal.Free
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Irrational
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.MetricSpace.IsometricSMul


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-! ## Equidecomposability calculus -/

/-- Two sets are congruent by finitely many isometries: there is a bijection from `A`
onto `B` that agrees pointwise with one of finitely many ambient isometries. -/
def btCongr {X : Type*} [MetricSpace X] (A B : Set X) : Prop :=
  ∃ (f : X → X) (S : Set (X ≃ᵢ X)),
    S.Finite ∧ Set.BijOn f A B ∧ ∀ x ∈ A, ∃ g ∈ S, f x = g x

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
