/-
  Author: @toskua, Avocado
-/
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.PositiveLinearFunctional
import Mathlib.Analysis.CStarAlgebra.PositiveLinearMap
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Tactic.Positivity


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
