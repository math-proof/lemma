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
public import Theorem.MeasureTheory.Geometry.BanachTarski.Part11


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/MeasureTheory/Geometry/BanachTarski.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/
namespace MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted

/-- The four orbit pieces of the free locus. -/
def btQ₁ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₁}

def btQ₂ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₂}

def btQ₃ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₃}

def btQ₄ : Set btE :=
  {x | ∃ h : x ∈ btOmega, btGamma ⟨x, h⟩ ∈ btP₄}

end MathlibExt.MeasureTheory.Geometry.BanachTarskiWanted
