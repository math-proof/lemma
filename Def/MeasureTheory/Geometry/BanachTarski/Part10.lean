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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part9


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The orbit relation of the action on the free locus. -/
def btOrbitRel : Setoid {x : btE // x ∈ btOmega} where
  r x y := ∃ w : FreeGroup (Fin 2), btAct w x.val = y.val
  iseqv := {
    refl := fun x => ⟨1, by simp [btAct_one x.val]⟩
    symm := fun {x y} h => by
      obtain ⟨w, hw⟩ := h
      refine ⟨w⁻¹, ?_⟩
      have e := btAct_inv w x.val
      rw [hw] at e
      exact e
    trans := fun {x y z} h1 h2 => by
      obtain ⟨w1, hw1⟩ := h1
      obtain ⟨w2, hw2⟩ := h2
      refine ⟨w2 * w1, ?_⟩
      rw [btAct_mul, hw1, hw2] }

/-- Orbit representative. -/
noncomputable def btRep (x : {x : btE // x ∈ btOmega}) : {x : btE // x ∈ btOmega} :=
  Quotient.out (Quotient.mk btOrbitRel x)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
