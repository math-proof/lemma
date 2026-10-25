/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finrank
import Abbrev.GroupTheory.TwoPowerRank
/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/


namespace AbelianGroup

noncomputable instance (A : Type*) [AddCommGroup A] (j : ℕ) [hj : Fact (0 < j)] :
    Module (ZMod 2) (higherTwoPowerLayer A j) := by
  let H := twoPowerImage A (j - 1)
  let K := ((twoPowerImage A j).comap H.subtype).toAddSubgroup
  apply QuotientAddGroup.zmodModule
  intro x
  change 2 • (x : A) ∈ twoPowerImage A j
  rcases x.property with ⟨a, ha⟩
  refine ⟨a, ?_⟩
  rw [LinearMap.lsmul_apply] at ha ⊢
  rw [← ha]
  rw [two_nsmul, ← add_zsmul]
  congr 1
  have hpow : 2 ^ j = 2 ^ (j - 1) + 2 ^ (j - 1) := by
    rw [← Nat.two_pow_pred_mul_two hj.out, mul_two]
  exact_mod_cast hpow

end AbelianGroup
