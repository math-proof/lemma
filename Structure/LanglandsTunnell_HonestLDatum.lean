import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

open Complex Polynomial

namespace LanglandsTunnell

structure LDatum (ι : Type*) where

  norm : ι → ℕ

  euler : ι → ℂ[X]

  dual : ι → ℂ[X]

  gammaR : Multiset ℂ

  gammaC : Multiset ℂ

  gammaRDual : Multiset ℂ

  gammaCDual : Multiset ℂ

  abscissa : ℝ

  center : ℝ

  degree : ℕ

namespace LDatum

variable {ι : Type*} (D : LDatum ι)


end LDatum

end LanglandsTunnell

end
