/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/KMahlerFunction.lean -/


import sympy.atlas.NumberTheory.KMahlerFunction


namespace MetaMathlibExt

example :
    PowerSeries.coeff 4 (mahlerSubst (PowerSeries.mk fun n => (n : Complex)) 2 1) = 2 := by
  have h1 : (2 ^ 1 : ℕ) = 2 := by decide
  have h2 : (2 : ℕ) ∣ 4 := by decide
  have h3 : (4 : ℕ) / 2 = 2 := by decide
  simp [mahlerSubst, PowerSeries.coeff_mk, h1, h2, h3]

example :
    PowerSeries.coeff 3 (mahlerSubst (PowerSeries.mk fun n => (n : Complex)) 2 1) = 0 := by
  have h1 : (2 ^ 1 : ℕ) = 2 := by decide
  have h2 : ¬ (2 : ℕ) ∣ 3 := by decide
  simp [mahlerSubst, PowerSeries.coeff_mk, h1, h2]

example : IsKMahlerFunction 2 0 := by
  have h0 : mahlerSubst (0 : PowerSeries Complex) 2 0 = 0 := by
    ext n
    simp [mahlerSubst, PowerSeries.coeff_mk]
  refine ⟨le_rfl, 0, fun _ => 1, by simp, by simp, ?_⟩
  simp [h0]

end MetaMathlibExt
