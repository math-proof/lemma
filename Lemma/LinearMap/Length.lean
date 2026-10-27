import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma length_eq_length_submodule_add {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] (N : Submodule A M) : Module.length A M = Module.length A ↥N + Module.length A (M ⧸ N) :=
  Module.length_eq_add_of_exact N.subtype N.mkQ (Submodule.injective_subtype N) (Submodule.mkQ_surjective N) (LinearMap.exact_subtype_mkQ N)
private lemma length_quotient_eq_add {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] {P Q : Submodule A M} (h : P ≤ Q) : Module.length A (M ⧸ P) = Module.length A ↥(Q.map P.mkQ) + Module.length A (M ⧸ Q) := by
  rw [length_eq_length_submodule_add (Q.map P.mkQ), (Submodule.quotientQuotientEquivQuotient P Q h).length_eq]
private lemma length_map_mkQ_range {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M] (P : Submodule A M) {N' : Type*} [AddCommGroup N'] [Module A N'] (g : N' →ₗ[A] M) : Module.length A ↥((LinearMap.range g).map P.mkQ) = Module.length A (N' ⧸ LinearMap.ker (LinearMap.comp P.mkQ g)) := by
  rw [← LinearMap.range_comp]
  apply (LinearMap.quotKerEquivRange (LinearMap.comp P.mkQ g)).length_eq.symm
private lemma det_ne_zero_of_injective {A : Type*} [CommRing A] [IsDomain A] {r : ℕ} (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (hφ : Function.Injective φ) : LinearMap.det φ ≠ 0 := by
  classical
  intro hdet
  rw [← LinearMap.det_toMatrix'] at hdet
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  rw [LinearMap.toMatrix'_mulVec] at hv0
  apply hv (hφ (hv0.trans (map_zero φ).symm))
private lemma smul_mem_range {A : Type*} [CommRing A] {r : ℕ} (φ : (Fin r → A) →ₗ[A] (Fin r → A)) (m : Fin r → A) : LinearMap.det φ • m ∈ LinearMap.range φ := by
  classical
  refine ⟨(LinearMap.toMatrix' φ).adjugate.mulVec m, ?_⟩
  rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec, LinearMap.det_toMatrix']
/--
[LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_length_quotient_range_eq_of_injective_of_comp_eq_comp.lean)
-/
@[path]
private lemma main
  {A : Type u} {r : ℕ} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (F₁ F₂ φ : (Fin r → A) →ₗ[A] (Fin r → A))
  -- given
  (hF₁ : Function.Injective F₁) (hφ : Function.Injective φ)
  (hcomm : LinearMap.comp φ F₂ = LinearMap.comp F₁ φ) :
  -- imply
  Module.length A ((Fin r → A) ⧸ LinearMap.range F₁) = Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by
  -- proof
  classical
  set N : Submodule A (Fin r → A) := LinearMap.range φ with hN
  set P : Submodule A (Fin r → A) := LinearMap.range (LinearMap.comp F₁ φ) with hP
  have hP1 : P ≤ LinearMap.range F₁ := LinearMap.range_comp_le_range φ F₁
  have hP2 : P ≤ N := by
    rw [hP, ← hcomm]
    apply LinearMap.range_comp_le_range F₂ φ
  have ha := length_quotient_eq_add hP1
  have hb := length_quotient_eq_add hP2
  have ha' : Module.length A ↥((LinearMap.range F₁).map P.mkQ) = Module.length A ((Fin r → A) ⧸ N) := by
    rw [length_map_mkQ_range]
    apply (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ, hP, LinearMap.range_comp, Submodule.comap_map_eq_of_injective hF₁])).length_eq
  have hb' : Module.length A ↥(N.map P.mkQ) = Module.length A ((Fin r → A) ⧸ LinearMap.range F₂) := by
    rw [hN, length_map_mkQ_range]
    apply (Submodule.quotEquivOfEq _ _ (by rw [LinearMap.ker_comp, Submodule.ker_mkQ, hP, ← hcomm, LinearMap.range_comp, Submodule.comap_map_eq_of_injective hφ])).length_eq
  have hfin : Module.length A ((Fin r → A) ⧸ N) ≠ ⊤ := by
    set d := LinearMap.det φ with hd
    have hd0 : d ≠ 0 := det_ne_zero_of_injective φ hφ
    let D : Submodule A (Fin r → A) := Submodule.pi Set.univ (fun _ : Fin r => (Ideal.span {d} : Submodule A A))
    have hDN : D ≤ N := by
      intro m hm
      rw [Submodule.mem_pi] at hm
      choose a ha using fun i => Ideal.mem_span_singleton'.1 (hm i (Set.mem_univ i))
      have hm' : m = d • a := by
        funext i
        rw [Pi.smul_apply, smul_eq_mul, mul_comm, ha i]
      rw [hm']
      apply smul_mem_range φ a
    apply ne_top_of_le_ne_top _ (Module.length_le_of_surjective (Submodule.factor hDN) (Submodule.factor_surjective hDN))
    rw [(Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
    apply WithTop.sum_ne_top.2 fun i _ => Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hd0)
  rw [ha', add_comm] at ha
  rw [hb'] at hb
  apply WithTop.add_right_cancel hfin (ha.symm.trans hb)


-- created on 2026-10-20
