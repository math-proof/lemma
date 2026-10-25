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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part15


namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- Two sets are finitely equidecomposable by global bijective isometries
partitioning each into pairwise-disjoint pieces with matching images. -/
def FinitelyEquidecomposableByIsometries
    {X : Type*} [MetricSpace X] (A B : Set X) : Prop :=
  ∃ (n : ℕ) (As : Fin n → Set X) (Bs : Fin n → Set X) (gs : Fin n → X ≃ᵢ X),
    (∀ i j, i ≠ j → Disjoint (As i) (As j)) ∧
    (∀ i j, i ≠ j → Disjoint (Bs i) (Bs j)) ∧
    (⋃ i, As i) = A ∧
    (⋃ i, Bs i) = B ∧
    ∀ i, (gs i : X → X) '' As i = Bs i

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
