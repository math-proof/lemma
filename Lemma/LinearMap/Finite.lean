import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_injective_linearMap {R : Type u} [CommRing R] {K0 K1 E0 E1 S0 S1 : Type u} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1] [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1] [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1] (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1) (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1) (hi : LinearMap.comp dE i0 = LinearMap.comp i1 dK) (hp : LinearMap.comp dS p0 = LinearMap.comp p1 dE) (hi1 : Function.Injective i1) (hp0 : Function.Surjective p0) (hex0 : LinearMap.range i0 = LinearMap.ker p0) (hex1 : LinearMap.range i1 = LinearMap.ker p1) (hE : LinearMap.ker dE = ⊥) : ∃ δ : LinearMap.ker dS →ₗ[R] (K1 ⧸ LinearMap.range dK), Function.Injective δ := by
  classical
  have step : ∀ s : LinearMap.ker dS, ∃ k : K1, ∃ e : E0, p0 e = s ∧ dE e = i1 k := by
    intro s
    obtain ⟨e, he⟩ := hp0 s
    have : dE e ∈ LinearMap.ker p1 := by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← hp, LinearMap.comp_apply, he]
      apply s.2
    rw [← hex1] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, e, he, hk.symm⟩
  choose kOf eOf hpe hde using step
  have well : ∀ (s : LinearMap.ker dS) (k : K1) (e : E0), p0 e = s → dE e = i1 k → (Submodule.Quotient.mk k : K1 ⧸ LinearMap.range dK) = Submodule.Quotient.mk (kOf s) := by
    intro s k e he hde'
    have hdiff : e - eOf s ∈ LinearMap.ker p0 := by
      rw [LinearMap.mem_ker, map_sub, he, hpe, sub_self]
    rw [← hex0] at hdiff
    obtain ⟨x, hx⟩ := hdiff
    rw [Submodule.Quotient.eq]
    refine ⟨x, hi1 ?_⟩
    have h1 : i1 (dK x) = dE (i0 x) := (LinearMap.congr_fun hi x).symm
    rw [h1, hx, map_sub, hde', hde, map_sub]
  refine ⟨(LinearMap.mk (fun s => Submodule.Quotient.mk (kOf s)) ?_ ?_ : LinearMap.ker dS →ₗ[R] (K1 ⧸ LinearMap.range dK)), ?_⟩
  ·
    intro s t
    show (Submodule.Quotient.mk (kOf (s + t)) : K1 ⧸ LinearMap.range dK) = Submodule.Quotient.mk (kOf s) + Submodule.Quotient.mk (kOf t)
    rw [← Submodule.Quotient.mk_add]
    apply (well (s + t) (kOf s + kOf t) (eOf s + eOf t) _ _).symm
    ·
      rw [map_add, hpe, hpe]
      rfl
    ·
      rw [map_add, hde, hde, map_add]
  ·
    intro r s
    show (Submodule.Quotient.mk (kOf (r • s)) : K1 ⧸ LinearMap.range dK) = r • Submodule.Quotient.mk (kOf s)
    rw [← Submodule.Quotient.mk_smul]
    apply (well (r • s) (r • kOf s) (r • eOf s) _ _).symm
    ·
      rw [map_smul, hpe]
      rfl
    ·
      rw [map_smul, hde, map_smul]
  ·
    intro s t hst
    have key : ∀ s : LinearMap.ker dS, (Submodule.Quotient.mk (kOf s) : K1 ⧸ LinearMap.range dK) = 0 → s = 0 := by
      intro s hs
      rw [Submodule.Quotient.mk_eq_zero] at hs
      obtain ⟨x, hx⟩ := hs
      have : eOf s - i0 x ∈ LinearMap.ker dE := by
        have h2 : dE (i0 x) = i1 (dK x) := LinearMap.congr_fun hi x
        rw [LinearMap.mem_ker, map_sub, hde, ← hx, h2, sub_self]
      rw [hE, Submodule.mem_bot, sub_eq_zero] at this
      apply Subtype.ext
      rw [← hpe s, this]
      have hmem : i0 x ∈ LinearMap.ker p0 := by
        rw [← hex0]
        apply LinearMap.mem_range_self i0 x
      rw [LinearMap.mem_ker] at hmem
      rw [hmem]
      rfl
    have hpsub : p0 (eOf s - eOf t) = s - t := by
      rw [map_sub, hpe, hpe]
      rfl
    have hdsub : dE (eOf s - eOf t) = i1 (kOf s - kOf t) := by
      rw [map_sub, hde, hde, map_sub]
    have hsub : (Submodule.Quotient.mk (kOf (s - t)) : K1 ⧸ LinearMap.range dK) = Submodule.Quotient.mk (kOf s) - Submodule.Quotient.mk (kOf t) := by
      rw [← Submodule.Quotient.mk_sub]
      apply (well (s - t) (kOf s - kOf t) (eOf s - eOf t) hpsub hdsub).symm
    apply sub_eq_zero.mp (key (s - t) _)
    rw [hsub]
    apply sub_eq_zero.mpr hst
/--
[TwoChartCech_kerMap_injective_of_H0_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TwoChartCech_kerMap_injective_of_H0_eq_zero.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsNoetherianRing R]
  {K0 K1 E0 E1 S0 S1 : Type u} [AddCommGroup K0] [Module R K0] [AddCommGroup K1] [Module R K1] [AddCommGroup E0] [Module R E0] [AddCommGroup E1] [Module R E1] [AddCommGroup S0] [Module R S0] [AddCommGroup S1] [Module R S1]
  (dK : K0 →ₗ[R] K1) (dE : E0 →ₗ[R] E1) (dS : S0 →ₗ[R] S1)
  (i0 : K0 →ₗ[R] E0) (i1 : K1 →ₗ[R] E1) (p0 : E0 →ₗ[R] S0) (p1 : E1 →ₗ[R] S1)
  (hi : LinearMap.comp dE i0 = LinearMap.comp i1 dK) (hp : LinearMap.comp dS p0 = LinearMap.comp p1 dE)
  (_ : Function.Injective i0) (hi1 : Function.Injective i1)
  (hp0 : Function.Surjective p0) (_ : Function.Surjective p1)
  (hex0 : LinearMap.range i0 = LinearMap.ker p0) (hex1 : LinearMap.range i1 = LinearMap.ker p1)
  (hE : LinearMap.ker dE = ⊥) [Module.Finite R (K1 ⧸ LinearMap.range dK)] :
  -- imply
  Module.Finite R (LinearMap.ker dS) := by
  -- proof
  obtain ⟨δ, hδ⟩ := exists_injective_linearMap dK dE dS i0 i1 p0 p1 hi hp hi1 hp0 hex0 hex1 hE
  apply Module.Finite.of_injective δ hδ


-- created on 2026-10-20
