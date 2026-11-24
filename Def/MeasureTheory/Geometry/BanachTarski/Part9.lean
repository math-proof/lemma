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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-! ## Bad set, free locus, and the paradoxical pieces of `F₂` -/

/-- Points fixed by some nontrivial word. -/
def btBad : Set btE :=
  {z | z ≠ 0 ∧ ∃ w : FreeGroup (Fin 2), w ≠ 1 ∧ btAct w z = z}

/-- The free locus: the unit ball minus the centre and the bad axes. -/
def btOmega : Set btE :=
  Metric.closedBall (0 : btE) 1 \ ({0} ∪ btBad)

/-- Words whose reduced form starts with a given letter. -/
def btW (s : Fin 2 × Bool) : Set (FreeGroup (Fin 2)) :=
  {w | w.toWord.head? = some s}

/-- Nonpositive powers of the inverse of the first generator. -/
def btT : Set (FreeGroup (Fin 2)) :=
  Set.range (fun n : ℕ => (FreeGroup.of (0 : Fin 2))⁻¹ ^ n)

/-- The four paradoxical pieces of the free group. -/
def btP₁ : Set (FreeGroup (Fin 2)) := btW (0, true) ∪ btT

def btP₂ : Set (FreeGroup (Fin 2)) := btW (0, false) \ btT

def btP₃ : Set (FreeGroup (Fin 2)) := btW (1, true)

def btP₄ : Set (FreeGroup (Fin 2)) := btW (1, false)

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
