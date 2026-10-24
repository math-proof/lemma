/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/TwoPowerRank.lean -/

import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Higher two-power ranks of finite abelian groups

This module defines `2^(j-1) A / 2^j A` as an `F₂`-vector space and uses its
dimension to define the source convention `rk_(2^j) A` for positive `j`.
-/

namespace AbelianGroup

/-- The subgroup `2^k A` of an additive commutative group. -/
def twoPowerImage (A : Type*) [AddCommGroup A] (k : ℕ) : Submodule ℤ A :=
  LinearMap.range (LinearMap.lsmul ℤ A (2 ^ k : ℤ))

/-- For positive `j`, the additive quotient `2^(j-1) A / 2^j A`. -/
abbrev higherTwoPowerLayer (A : Type*) [AddCommGroup A] (j : ℕ) : Type _ :=
  twoPowerImage A (j - 1) ⧸
    ((twoPowerImage A j).comap (twoPowerImage A (j - 1)).subtype).toAddSubgroup

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

/-- For positive `j`, the `2^j`-rank of a finite abelian group `A` is the
`F₂`-dimension of `2^(j-1) A / 2^j A`. -/
noncomputable def higherTwoPowerRank (A : Type*) [AddCommGroup A] [Finite A]
    (j : ℕ) (hj : 0 < j) : ℕ :=
  letI : Fact (0 < j) := ⟨hj⟩
  Module.finrank (ZMod 2) (higherTwoPowerLayer A j)

/-- The `4`-rank is the `F₂`-dimension of `2A / 4A`. -/
noncomputable abbrev fourRank (A : Type*) [AddCommGroup A] [Finite A] : ℕ :=
  higherTwoPowerRank A 2 (by norm_num)
end AbelianGroup
