-- Author: @toskua, Avocado
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.PSeries


namespace SpecialFunctions.CatalanSqrtTwo

open scoped Topology

open Finset Nat Filter Real

/-- Catalan's product term: `(4m+2)^2 / ((4m+1) * (4m+3))`. -/
noncomputable def catalanTerm (m : ℕ) : ℝ :=
  (((4 * m + 2 : ℕ) : ℝ) ^ 2) /
    (((4 * m + 1 : ℕ) : ℝ) * ((4 * m + 3 : ℕ) : ℝ))

end SpecialFunctions.CatalanSqrtTwo
