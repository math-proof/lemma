/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.MeasureTheory.Function.LpSeminorm.Count
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Theorem.Analysis.NormedSpace.RieszThorin


section

open MeasureTheory

namespace FunctionalAnalysis.RieszThorinWanted

noncomputable def sgn {κ : Type*} (y : κ → Complex) (i : κ) : Complex :=
  if y i = 0 then 0 else (starRingEnd ℂ) (y i) / (‖y i‖ : ℂ)

end FunctionalAnalysis.RieszThorinWanted
end
