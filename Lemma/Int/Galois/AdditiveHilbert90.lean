import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.Galois.AdditiveHilbert90
open Algebra


namespace Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
/--
[pow_fix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
omit [FiniteDimensional K L] [IsGalois K L] in
private lemma pow_fix (σ : L ≃ₐ[K] L) (x : L) (hx : σ x = x) (n : ℕ) :
  (σ ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, AlgEquiv.mul_apply, hx, ih]

end Algebra

namespace Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
/--
[inv_pow_fix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
omit [FiniteDimensional K L] [IsGalois K L] in
private lemma inv_pow_fix (σ : L ≃ₐ[K] L) (x : L) (hx : σ x = x) (n : ℕ) :
  ((σ ^ n)⁻¹) x = x := by
  have hinv : σ⁻¹ x = x := by
    have h1 : (σ⁻¹ * σ) x = x := by rw [inv_mul_cancel, AlgEquiv.one_apply]
    rw [AlgEquiv.mul_apply] at h1
    rwa [hx] at h1
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_inv_rev, AlgEquiv.mul_apply, ih, hinv]

end Algebra

namespace Algebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
/--
[zpow_fix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
omit [FiniteDimensional K L] [IsGalois K L] in
private lemma zpow_fix (σ : L ≃ₐ[K] L) (x : L) (hx : σ x = x) (n : ℤ) :
  (σ ^ n) x = x := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast]
    exact pow_fix σ x hx m
  · rw [zpow_neg, zpow_natCast]
    exact inv_pow_fix σ x hx m

end Algebra

namespace Algebra

/--
[ker_trace_eq_range_algEquiv_sub_id](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
lemma ker_trace_eq_range_algEquiv_sub_id
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
-- given
  (σ : L ≃ₐ[K] L)
  (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
-- imply
  LinearMap.ker (Algebra.trace K L) =
    LinearMap.range (σ.toLinearMap - LinearMap.id) := by
-- proof
  have hle : LinearMap.range (σ.toLinearMap - LinearMap.id) ≤
    LinearMap.ker (Algebra.trace K L) := by
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [LinearMap.mem_ker, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply,
      LinearMap.id_apply, map_sub, Algebra.trace_eq_of_algEquiv, sub_self]
  have hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) =
    (⊥ : IntermediateField K L).toSubmodule := by
    ext x
    have hmem : (x ∈ (⊥ : IntermediateField K L).toSubmodule) ↔
      x ∈ (⊥ : IntermediateField K L) :=
      Iff.rfl
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, AlgEquiv.toLinearMap_apply,
      LinearMap.id_apply, sub_eq_zero, hmem, IsGalois.mem_bot_iff_fixed]
    constructor
    · intro hx τ
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hσ τ)
      rw [← hn]
      exact zpow_fix σ x hx n
    · intro hx
      exact hx σ
  have hrange_top : LinearMap.range (Algebra.trace K L) = ⊤ :=
    LinearMap.range_eq_top.mpr (Algebra.trace_surjective K L)
  have htr1 : Module.finrank K (LinearMap.range (Algebra.trace K L)) = 1 := by
    rw [hrange_top, finrank_top]
    exact Module.finrank_self K
  have hker1 :
    Module.finrank K (LinearMap.ker (σ.toLinearMap - LinearMap.id)) = 1 := by
    rwa [hker]
  have hdim1 := LinearMap.finrank_range_add_finrank_ker (σ.toLinearMap - LinearMap.id)
  have hdim2 := LinearMap.finrank_range_add_finrank_ker (Algebra.trace K L)
  have hfin : Module.finrank K (LinearMap.ker (Algebra.trace K L)) ≤
    Module.finrank K (LinearMap.range (σ.toLinearMap - LinearMap.id)) := by
    omega
  exact (Submodule.eq_of_le_of_finrank_le hle hfin).symm

end Algebra

namespace Algebra

/--
[exists_algEquiv_sub_eq_of_trace_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/Galois/AdditiveHilbert90.lean)
-/
@[path]
lemma exists_algEquiv_sub_eq_of_trace_eq_zero
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  {x : L}
-- given
  (σ : L ≃ₐ[K] L)
  (hσ : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
  (hx : Algebra.trace K L x = 0) :
-- imply
  ∃ y : L, σ y - y = x := by
-- proof
  have hmem : x ∈ LinearMap.ker (Algebra.trace K L) := LinearMap.mem_ker.mpr hx
  rw [ker_trace_eq_range_algEquiv_sub_id σ hσ] at hmem
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hmem
  exact ⟨y, by
    simpa only [LinearMap.sub_apply, AlgEquiv.toLinearMap_apply, LinearMap.id_apply]
      using hy⟩

end Algebra


-- created on 2026-10-20
-- updated on 2026-10-23
