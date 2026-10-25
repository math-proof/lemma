/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/BilinearForm/DualLocalization.lean -/


import Lemma.Matrix.BilinearForm.DualLocalization
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Tactic.NormNum


open LinearMap.BilinForm in
/-- Generic theorem applies with `S = ⊥`, the trivial localization at 1. -/
example {A K V : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
    [IsScalarTower A K V] (B : LinearMap.BilinForm K V) (M : Submodule A V)
    (hM : M.FG) :
    B.dualSubmodule (Submodule.span
        (Localization.subalgebra.ofField K (⊥ : Submonoid A)
          (bot_le : (⊥ : Submonoid A) ≤ nonZeroDivisors A)) (M : Set V)) =
      Submodule.span (Localization.subalgebra.ofField K (⊥ : Submonoid A)
        (bot_le : (⊥ : Submonoid A) ≤ nonZeroDivisors A))
        (B.dualSubmodule M : Set V) :=
  dualSubmodule_span_localization B (⊥ : Submonoid A)
    (bot_le : (⊥ : Submonoid A) ≤ nonZeroDivisors A) M hM

open LinearMap.BilinForm in
/-- The theorem needs no nondegeneracy: it holds for the zero form. -/
example {A K V : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] [AddCommGroup V] [Module A V] [Module K V]
    [IsScalarTower A K V] (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)
    (M : Submodule A V) (hM : M.FG) :
    (0 : LinearMap.BilinForm K V).dualSubmodule (Submodule.span
        (Localization.subalgebra.ofField K S hS) (M : Set V)) =
      Submodule.span (Localization.subalgebra.ofField K S hS)
        ((0 : LinearMap.BilinForm K V).dualSubmodule M : Set V) :=
  dualSubmodule_span_localization 0 S hS M hM

open LinearMap.BilinForm in
/-- Nontrivial localization: with `A = ℤ`, `K = V = ℚ`, `S` the powers of `2`,
the multiplication form, and the lattice `M = ℤ`, the fraction `1 / 2` lies in
the dual of the localized span, with denominator cleared by `2 • (1 / 2) = 1`. -/
example : (1 / 2 : ℚ) ∈ LinearMap.BilinForm.dualSubmodule
    (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ)
    (Submodule.span
      (Localization.subalgebra.ofField ℚ (Submonoid.powers (2 : ℤ))
        (by rw [Submonoid.powers_le, mem_nonZeroDivisors_iff_ne_zero]; norm_num))
      ((1 : Submodule ℤ ℚ) : Set ℚ))
    ∧ (2 : ℤ) • (1 / 2 : ℚ) ∈ LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ) (1 : Submodule ℤ ℚ) := by
  have hS : Submonoid.powers (2 : ℤ) ≤ nonZeroDivisors ℤ := by
    rw [Submonoid.powers_le, mem_nonZeroDivisors_iff_ne_zero]; norm_num
  have hM : ((1 : Submodule ℤ ℚ)).FG := by
    rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton 1
  have h1 : (1 : ℚ) ∈ LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ) (1 : Submodule ℤ ℚ) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    simp only [LinearMap.mul_apply']
    simpa using hy
  have hclear : (2 : ℤ) • (1 / 2 : ℚ) ∈ LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ) (1 : Submodule ℤ ℚ) := by
    have heq : (2 : ℤ) • (1 / 2 : ℚ) = 1 := by norm_num
    rw [heq]
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro y hy
    simp only [LinearMap.mul_apply']
    simpa using hy
  have hloc : (1 / 2 : ℚ) ∈ LinearMap.BilinForm.dualSubmodule
      (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ)
      (Submodule.span
        (Localization.subalgebra.ofField ℚ (Submonoid.powers (2 : ℤ))
          (by rw [Submonoid.powers_le, mem_nonZeroDivisors_iff_ne_zero]; norm_num))
        ((1 : Submodule ℤ ℚ) : Set ℚ)) := by
    have hEq := LinearMap.BilinForm.dualSubmodule_span_localization
      (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ)
      (Submonoid.powers (2 : ℤ)) hS (1 : Submodule ℤ ℚ) hM
    simp only at hEq
    rw [hEq]
    have hmem : (1 / 2 : ℚ) ∈ Localization.subalgebra.ofField ℚ
        (Submonoid.powers (2 : ℤ)) hS := by
      refine ⟨1, 2, Submonoid.mem_powers 2, ?_⟩
      push_cast
      norm_num
    let c : Localization.subalgebra.ofField ℚ (Submonoid.powers (2 : ℤ)) hS :=
      ⟨1 / 2, hmem⟩
    have hcoe : ((c : ℚ)) = (1 / 2 : ℚ) := rfl
    have hsc : c • (1 : ℚ) = (1 / 2 : ℚ) := by
      have h := Subalgebra.smul_def c (1 : ℚ)
      rw [h, hcoe]
      simp
    have hspan : c • (1 : ℚ) ∈ Submodule.span
        (Localization.subalgebra.ofField ℚ (Submonoid.powers (2 : ℤ)) hS)
        ((LinearMap.BilinForm.dualSubmodule (LinearMap.mul ℚ ℚ : LinearMap.BilinForm ℚ ℚ)
          (1 : Submodule ℤ ℚ)) : Set ℚ) :=
      Submodule.smul_mem _ _ (Submodule.subset_span h1)
    rw [← hsc]
    exact hspan
  exact ⟨hloc, hclear⟩

