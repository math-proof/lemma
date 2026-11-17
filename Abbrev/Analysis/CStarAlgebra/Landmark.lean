/-
  Author: @toskua, Avocado
-/
module

public import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
public import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpHolder
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Tactic.Positivity

@[expose] public section


section

open scoped InnerProductSpace ComplexOrder

universe u

namespace Analysis.CStarAlgebra.LandmarkWanted

-- Helper predicates allowed; no forbidden constructs.

/-- The Hilbert space carrying the universal GNS representation: the l^2 direct sum of the
GNS spaces of all positive linear functionals. -/
noncomputable abbrev UH (A : Type u) [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] : Type u :=
  ↥(lp (fun f : A →ₚ[ℂ] ℂ => f.GNS) 2)

end Analysis.CStarAlgebra.LandmarkWanted
end
