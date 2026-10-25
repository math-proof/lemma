/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Algebra.Group.AddChar
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Def.GroupTheory.FiniteAbelianDual


namespace MathlibExt.GroupTheory.FiniteAbelianDualWanted

open scoped DirectSum

theorem dual_zmodFamilyHom_injective {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    Function.Injective (dual_zmodFamilyHom n) := by
  intro u v h
  ext i
  apply AddChar.zmodAddEquiv.injective
  exact congrFun h i

theorem dual_zmodDirectSumHom_injective {ι : Type*} [DecidableEq ι]
    (n : ι → ℕ) [∀ i, NeZero (n i)] :
    Function.Injective (dual_zmodDirectSumHom n) :=
  AddChar.directSum_injective.comp (dual_zmodFamilyHom_injective n)

end MathlibExt.GroupTheory.FiniteAbelianDualWanted
