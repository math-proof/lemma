import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Lemma.ModularCurve.X0
import Def.ModularCurve_GenusNumerics

namespace ModularCurve


@[simp]
lemma cuspCount_one : cuspCount 1 = 1 := by
  simp [cuspCount]

end ModularCurve
