import Mathlib
import sympy.Basic
open Polynomial


/-- ported from external source -/

noncomputable def restr
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  (L : Submodule ℤ V) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) : Module.End ℤ L :=
  (T.restrictScalars ℤ).restrict hTL

private lemma  coe_restr_apply
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  (L : Submodule ℤ V) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L) (x : L) :
  ((restr L T hTL x : L) : V) = T x := rfl

private lemma  coe_restr_pow_apply
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  (L : Submodule ℤ V) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L)
  (n : ℕ) (x : L) : (((restr L T hTL ^ n) x : L) : V) = (T ^ n) (x : V) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, coe_restr_apply]

private lemma  coe_aeval_restr_apply
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  (L : Submodule ℤ V) (T : V →ₗ[ℂ] V) (hTL : ∀ x ∈ L, T x ∈ L)
  (P : ℤ[X]) (x : L) :
  ((aeval (restr L T hTL) P x : L) : V) = aeval T (P.map (algebraMap ℤ ℂ)) (x : V) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, Submodule.coe_add, hp, hq, Polynomial.map_add, map_add,
      LinearMap.add_apply]
  | monomial n a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, Submodule.coe_smul,
      coe_restr_pow_apply, Polynomial.map_monomial, aeval_monomial, Module.End.mul_apply,
      Module.algebraMap_end_apply, eq_intCast, Int.cast_smul_eq_zsmul]

private lemma  isIntegral_of_mem_span_of_apply_eq_smul
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  (L : Submodule ℤ V) (hfg : L.FG) (T : V →ₗ[ℂ] V)
  (hTL : ∀ x ∈ L, T x ∈ L) {v : V} (hv : v ∈ Submodule.span ℂ (L : Set V)) (hv0 : v ≠ 0)
  {c : ℂ} (hTv : T v = c • v) : IsIntegral ℤ c := by
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hfg
  obtain ⟨P, hPm, hP⟩ := LinearMap.exists_monic_and_aeval_eq_zero ℤ (restr L T hTL)
  have hL : ∀ x ∈ L, aeval T (P.map (algebraMap ℤ ℂ)) x = 0 := by
    intro x hx
    have h := coe_aeval_restr_apply L T hTL P ⟨x, hx⟩
    rw [hP, LinearMap.zero_apply, Submodule.coe_zero] at h
    apply h.symm
  have hker : Submodule.span ℂ (L : Set V) ≤ LinearMap.ker (aeval T (P.map (algebraMap ℤ ℂ))) :=
    Submodule.span_le.mpr fun x hx => LinearMap.mem_ker.mpr (hL x hx)
  have hv' : aeval T (P.map (algebraMap ℤ ℂ)) v = 0 := LinearMap.mem_ker.mp (hker hv)
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul hTv, smul_eq_zero] at hv'
  have hroot : (P.map (algebraMap ℤ ℂ)).eval c = 0 := hv'.resolve_right hv0
  exact ⟨P, hPm, by rwa [eval_map] at hroot⟩
@[path]
private lemma main
  [AddCommGroup V] [Module ℂ V]
  {L : Submodule ℤ V}
  {T : V →ₗ[ℂ] V}
  {v : V}
  {c : ℂ}
-- given
  (hfg : L.FG)
  (hTL : ∀ x ∈ L, T x ∈ L)
  (hv : v ∈ Submodule.span ℂ (L : Set V))
  (hv0 : v ≠ 0)
  (hTv : T v = c • v) :
-- imply
  IsIntegral ℤ c :=
-- proof
  isIntegral_of_mem_span_of_apply_eq_smul L hfg T hTL hv hv0 hTv


-- created on 2026-10-23
