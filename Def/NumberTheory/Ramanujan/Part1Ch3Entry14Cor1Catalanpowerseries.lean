/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14Cor1Catalanpowerseries.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.RingTheory.PowerSeries.Catalan
import Lemma.Finset.Enumerative.CatalanGeneratingFunction
/-!
# Ramanujan's Notebooks, Part I, Chapter 3

Statements and selected subresults from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry14Cor1Catalanpowerseries

/-- Product `∏_{j ∈ Ico (k+1) (2k)} (n + j)`, syntactically the product in the Wanted term. -/
noncomputable def rcatProd (n : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.Ico (k + 1) (2 * k), (n + (j : ℝ))

/-- Coefficient `e_k(n)`: `1` at `k = 0`, else `n * rcatProd n k / k!`. -/
noncomputable def rcatCoeff (n : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else n * rcatProd n k / (Nat.factorial k : ℝ)

/-- Catalan power series over `ℝ`. -/
noncomputable def rcatR : PowerSeries ℝ :=
  PowerSeries.map (Nat.castRingHom ℝ) PowerSeries.catalanSeries

/-- The power series `F_n(a) = ∑' k, rcatCoeff n k * a ^ k`. -/
noncomputable def rcatF (n a : ℝ) : ℝ :=
  ∑' k : ℕ, rcatCoeff n k * a ^ k

/-- Polynomial version of `rcatCoeff · k`, used only for the real-exponent convolution. -/
noncomputable def rcatPoly (k : ℕ) : Polynomial ℝ :=
  if k = 0 then 1
  else Polynomial.C (1 / (Nat.factorial k : ℝ)) * Polynomial.X *
    ∏ j ∈ Finset.Ico (k + 1) (2 * k), (Polynomial.X + Polynomial.C (j : ℝ))

end Entry14Cor1Catalanpowerseries
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
end
