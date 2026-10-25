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
import Theorem.MeasureTheory.Geometry.BanachTarski.Part8


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
