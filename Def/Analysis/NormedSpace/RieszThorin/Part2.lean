/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.MeasureTheory.Function.LpSeminorm.Count
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Theorem.Analysis.NormedSpace.RieszThorin.Part2

@[expose] public section

section

open MeasureTheory

namespace FunctionalAnalysis.RieszThorinWanted

noncomputable def ph {α : Type*} (h : α → Complex) (i : α) : Complex :=
  if h i = 0 then 0 else h i / (‖h i‖ : ℂ)

end FunctionalAnalysis.RieszThorinWanted
end
