import Lemma.ModularCurve.AtkinLehner
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Height.NumberField
import Lemma.Compat.Mathlib430
import Instance.ModularCurve_JZeroNaiveHeight
import Def.ModularCurve_JZeroNaiveHeight

noncomputable section

open AlgebraicCurve Polynomial

namespace ModularCurve

variable (N : ℕ) [NeZero N]


variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]


variable {N K}

theorem jFactor_of_nonneg {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : 0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)) :
    jFactor N v = X - C (jCoord N v) :=
  if_pos hv

theorem jFactor_of_neg {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) < 0) :
    jFactor N v = 1 :=
  if_neg (not_le.mpr hv)

@[simp]
theorem symPoly_zero : symPoly N 0 = 1 :=
  Finsupp.prod_zero_index

theorem symPoly_single (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (n : ℤ) :
    symPoly N (Finsupp.single v n) = jFactor N v ^ n.toNat :=
  Finsupp.prod_single_index (by simp)

theorem divNaiveHeight_nonneg (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ divNaiveHeight N K g' D := by
  unfold divNaiveHeight
  split_ifs with h
  · exact Height.logHeight_nonneg _
  · exact le_rfl

theorem JZero.repHeights_nonneg {g' : ℕ} {c : ↥(JZero N ^+ ↥K.fixingSubgroup)} {r : ℝ}
    (hr : r ∈ JZero.repHeights N K g' c) : 0 ≤ r := by
  obtain ⟨D, E, -, -, -, -, rfl⟩ := hr
  exact divNaiveHeight_nonneg g' D

theorem JZero.naiveHeight_nonneg (g' : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup)) :
    0 ≤ JZero.naiveHeight N K g' c :=
  Real.sInf_nonneg fun _ hr => JZero.repHeights_nonneg hr

theorem JZero.naiveHeight_le (g' : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)))
    (hD : ∀ v, 0 ≤ D v)
    (hE : (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        + (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 = D)
    (hK : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ K.fixingSubgroup →
        arithmeticGalois (modularFunctionFieldFull N) σ • D = D)
    (hc : Pic0.mk E = (c : JZero N)) :
    JZero.naiveHeight N K g' c ≤ divNaiveHeight N K g' D :=
  csInf_le ⟨0, fun _ hr => JZero.repHeights_nonneg hr⟩ ⟨D, E, hD, hE, hK, hc, rfl⟩

theorem JZero.naiveHeight_eq_zero (g' : ℕ) (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
    (h : JZero.repHeights N K g' c = ∅) : JZero.naiveHeight N K g' c = 0 := by
  rw [JZero.naiveHeight, h, Real.sInf_empty]

end ModularCurve

end
