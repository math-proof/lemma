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
import Theorem.Analysis.NormedSpace.RieszThorin.Part2


section

open MeasureTheory

namespace FunctionalAnalysis.RieszThorinWanted

noncomputable def ph {α : Type*} (h : α → Complex) (i : α) : Complex :=
  if h i = 0 then 0 else h i / (‖h i‖ : ℂ)

end FunctionalAnalysis.RieszThorinWanted
end
