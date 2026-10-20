import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LindemannWeierstrass
open MathlibExt.NumberTheory.LindemannWeierstrassWanted


/--
[lindemann_weierstrass'](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LindemannWeierstrass.lean)
-/
@[path]
private lemma lindemann_weierstrass'_eq
  :
-- imply
  ∀ {ι : Type*} [Fintype ι] (α : ι → ℂ),
    Function.Injective α → (∀ i, IsAlgebraic ℚ (α i)) →
    ∀ (β : ι → ℂ), (∀ i, IsAlgebraic ℚ (β i)) → (∃ i, β i ≠ 0) →
    ∑ i, β i * Complex.exp (α i) ≠ 0 := by
-- proof
  apply MathlibExt.NumberTheory.LindemannWeierstrassWanted.lindemann_weierstrass'

/--
[lindemann_weierstrass](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LindemannWeierstrass.lean)
-/
@[path]
private lemma lindemann_weierstrass_eq
  :
-- imply
  ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (α : ι → ℂ),
    Function.Injective α → (∀ i, IsAlgebraic ℚ (α i)) →
    ∀ (β : ι → ℂ), (∀ i, IsAlgebraic ℚ (β i)) → (∃ i, β i ≠ 0) →
    ∑ i, β i * Complex.exp (α i) ≠ 0 := by
-- proof
  apply MathlibExt.NumberTheory.LindemannWeierstrassWanted.lindemann_weierstrass


-- created on 2026-10-20
