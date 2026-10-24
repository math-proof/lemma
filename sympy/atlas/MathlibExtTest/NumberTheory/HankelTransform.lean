/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/HankelTransform.lean -/


import sympy.atlas.NumberTheory.HankelTransform


namespace MetaMathlibExt

example {R : Type*} [CommRing R] (a : ℕ → R) : hankelTransform a 0 = a 0 := by
  simp [hankelTransform]

example {R : Type*} [CommRing R] (a : ℕ → R) :
    hankelTransform a 1 = a 0 * a 2 - a 1 * a 1 := by
  simp [hankelTransform, Matrix.det_fin_two]

example {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) (h : HasJacobiFraction a alpha beta mu0 F) :
    PowerSeries.mk a = PowerSeries.C mu0 * F 0 :=
  h.1

example {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) (h : HasJacobiFraction a alpha beta mu0 F) (i : ℕ) :
    (1 - PowerSeries.C (alpha i) * PowerSeries.X -
      PowerSeries.C (beta (i + 1)) * PowerSeries.X ^ 2 * F (i + 1)) * F i = 1 :=
  h.2 i

example {K : Type*} [Ring K] (a alpha beta : ℕ → K) (mu0 : K)
    (F : ℕ → PowerSeries K) (h : HasJacobiFraction a alpha beta mu0 F) :
    (1 - PowerSeries.C (alpha 0) * PowerSeries.X -
      PowerSeries.C (beta 1) * PowerSeries.X ^ 2 * F 1) * F 0 = 1 := by
  have := h.2 0
  simpa using this

#print axioms MetaMathlibExt.hankelTransform
#print axioms MetaMathlibExt.HasJacobiFraction

end MetaMathlibExt
