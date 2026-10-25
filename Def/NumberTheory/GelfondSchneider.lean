/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GelfondSchneider.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Tactic


section GS_N2
end GS_N2
section GS_AN
end GS_AN
section GS_JENSEN
end GS_JENSEN
section GS_NF
end GS_NF
section GS_SETUP
end GS_SETUP
section GS_DENOM
end GS_DENOM
section GS_NF2
end GS_NF2
section

namespace MathlibExt.NumberTheory.TranscendenceWanted

section GS_DEFS

/-- Frequency at column `t : Fin (L * L)` (same formula as in `gs_freq_injective`). -/
def gs_ω (b : ℂ) (L : ℕ) (t : Fin (L * L)) : ℂ :=
  ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : ℂ) +
    (((finProdFinEquiv (m := L) (n := L)).symm t).2.val : ℂ) * b)

/-- Frequency at column `t`, as an element of `K`. -/
def gs_ωK (K : Type*) [Field K] (L : ℕ) (bK : K) (t : Fin (L * L)) : K :=
  ((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : K) +
    (((finProdFinEquiv (m := L) (n := L)).symm t).2.val : K) * bK)

/-- Auxiliary ring-of-integers matrix entry. -/
def gs_e (K : Type*) [Field K] [NumberField K] (δ L : ℕ)
    (α' β' γ' : 𝓞 K) (E' k n : ℕ) (t : Fin (L * L)) : 𝓞 K :=
  (δ : 𝓞 K) ^ (E' - k - ((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n -
      ((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n) *
    (((((finProdFinEquiv (m := L) (n := L)).symm t).1.val : 𝓞 K)) * (δ : 𝓞 K) +
      ((((finProdFinEquiv (m := L) (n := L)).symm t).2.val : 𝓞 K)) * β') ^ k *
    α' ^ (((finProdFinEquiv (m := L) (n := L)).symm t).1.val * n) *
    γ' ^ (((finProdFinEquiv (m := L) (n := L)).symm t).2.val * n)

end GS_DEFS
end MathlibExt.NumberTheory.TranscendenceWanted
end
