/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/


import sympy.atlas.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion
import Lemma.Nat.QuadraticForms.ThreeSquaresLegendreRecursion


namespace MathlibExtTest.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion

-- At `p = 3`, the recursion computes the representations of `18` from those of `2`.
example : Nat.threeSquareRepresentationCount 18 = 36 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hleg : legendreSym 3 (-(2 : ℤ)) = 1 := by decide
  have hr : Nat.threeSquareRepresentationCount 2 = 12 := by decide
  have h := MetaMathlibExt.r3_legendre_recursion
    (p := 3) (n := 2) (α := 1) (by norm_num) (by norm_num)
  have h' : (Nat.threeSquareRepresentationCount 18 : ℤ) = 36 := by
    convert h using 1
    norm_num [hleg, hr]
  exact_mod_cast h'

-- When `3² ∣ 9`, the correction term gives `r₃(81) = 4 · 30 - 3 · 6`.
example : Nat.threeSquareRepresentationCount 81 = 102 := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hleg₁ : legendreSym 3 (-(1 : ℤ)) = -1 := by decide
  have hr₁ : Nat.threeSquareRepresentationCount 1 = 6 := by decide
  have h₉ := MetaMathlibExt.r3_legendre_recursion
    (p := 3) (n := 1) (α := 1) (by norm_num) (by norm_num)
  have h₉' : (Nat.threeSquareRepresentationCount 9 : ℤ) = 30 := by
    convert h₉ using 1
    norm_num [hleg₁, hr₁]
  have hr₉ : Nat.threeSquareRepresentationCount 9 = 30 := by exact_mod_cast h₉'
  have hleg₉ : legendreSym 3 (-(9 : ℤ)) = 0 := by decide
  have h := MetaMathlibExt.r3_legendre_recursion
    (p := 3) (n := 9) (α := 1) (by norm_num) (by norm_num)
  have h' : (Nat.threeSquareRepresentationCount 81 : ℤ) = 102 := by
    convert h using 1
    norm_num [hleg₉, hr₉, hr₁]
  exact_mod_cast h'

end MathlibExtTest.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion
