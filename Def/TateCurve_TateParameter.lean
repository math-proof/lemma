import Mathlib
import Def.TateCurve_QSeries

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter


open scoped NNReal

open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]


section TateParameter

variable [CompleteSpace K]

noncomputable def jInversionStep (j₀ q : K) : K :=
  (curve q).c₄ ^ 3 / j₀ - ((curve q).Δ - q)

end TateParameter

end TateCurve
