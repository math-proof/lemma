/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/GeneralizedCatalanSchroeder.lean -/


import Lemma.Finset.Enumerative.GeneralizedCatalanSchroeder
import Mathlib.Tactic.NormNum


open scoped BigOperators

namespace MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder

-- The Catalan specialization has `g = 1` and `f = X`.
example :
    PowerSeries.mk (fun n => (catalan n : ℚ)) =
      (1 : PowerSeries ℚ) * PowerSeries.subst PowerSeries.X
        (PowerSeries.mk (fun n => (catalan n : ℚ))) := by
  apply MetaMathlibExt.generalizedCatalanSchroeder_generatingFunction
      (R := ℚ) (s := 2) (t := 1) (p := 1)
  · norm_num
  · norm_num
  · intro n hn
    simpa using catalan_recurrence_rat n hn
  · norm_num
  · norm_num

-- The public recurrence lemma gives the Catalan quadratic functional equation.
example :
    PowerSeries.mk (fun n => (catalan n : ℚ)) - 1 =
      PowerSeries.C (1 : ℚ) * PowerSeries.X +
        PowerSeries.C (2 : ℚ) * PowerSeries.X *
          (PowerSeries.mk (fun n => (catalan n : ℚ)) - 1) +
            PowerSeries.C (1 : ℚ) * PowerSeries.X *
              (PowerSeries.mk (fun n => (catalan n : ℚ)) - 1) ^ 2 := by
  apply MetaMathlibExt.generalizedCatalanSchroeder_recurrence_functionalEquation
  · norm_num
  · norm_num
  · intro n hn
    simpa using catalan_recurrence_rat n hn

end MathlibExtTest.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
