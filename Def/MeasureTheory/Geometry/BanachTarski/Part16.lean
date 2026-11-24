module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.GroupTheory.FreeGroup.Reduce
public import Mathlib.SetTheory.Cardinal.Free
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Pi.Irrational
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part15


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
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
