import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineOpen_isLocalization_primeCompl_of_isPreimmersion_of_forall_specializes.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} [IsReduced X]
  {V : X.Opens}
  (x : X)
  (F : Type u) [Field F] [Algebra (X.presheaf.obj (op V)) F]
  (φ : Spec (CommRingCat.of F) ⟶ X) [IsPreimmersion φ]
  -- given
  (hV : IsAffineOpen V)
  (hxV : x ∈ V)
  (hmax : ∀ y : X, y ⤳ x → y = x)
  (hφx : φ.base (IsLocalRing.closedPoint F) = x)
  (hφ : Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op V)) F)) ≫ hV.fromSpec = φ) :
  -- imply
  IsLocalization (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl F := by
  -- proof
  classical
  have hpt : hV.fromSpec.base ((Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op V)) F))).base
      (IsLocalRing.closedPoint F)) = x := by
    rw [← hφx, ← hφ]
    rfl
  have h𝔭 : hV.primeIdealOf ⟨x, hxV⟩ =
      (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op V)) F))).base (IsLocalRing.closedPoint F) := by
    apply hV.fromSpec.isOpenEmbedding.injective
    rw [hpt]
    apply hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hmem : ∀ s : X.presheaf.obj (op V), s ∈ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal ↔
      algebraMap (X.presheaf.obj (op V)) F s = 0 := by
    intro s
    rw [h𝔭]
    change algebraMap (X.presheaf.obj (op V)) F s ∈ IsLocalRing.maximalIdeal F ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not]
  let _ : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op V)) F)) ≫ hV.fromSpec) := by
    rw [hφ]
    infer_instance
  have hpre : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.obj (op V)) F))) :=
    IsPreimmersion.of_comp _ hV.fromSpec
  have hsos : (algebraMap (X.presheaf.obj (op V)) F).SurjectiveOnStalks :=
    ((IsPreimmersion.SpecMap_iff _).mp hpre).2
  set 𝔭 := hV.primeIdealOf ⟨x, hxV⟩ with h𝔭def
  have hkill : ∀ d ∈ 𝔭.asIdeal, ∃ c : 𝔭.asIdeal.primeCompl, (c : X.presheaf.obj (op V)) * d = 0 := by
    intro d hd
    set L := Localization.AtPrime 𝔭.asIdeal with hL
    have huniq : ∀ Q : Ideal L, Q.IsPrime → Q = IsLocalRing.maximalIdeal L := by
      intro Q hQ
      let q : PrimeSpectrum (X.presheaf.obj (op V)) := ⟨Q.comap (algebraMap (X.presheaf.obj (op V)) L), Ideal.IsPrime.comap _⟩
      have hq𝔭 : q ≤ 𝔭 := by
        intro s hs
        by_contra hs'
        apply hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hs
          (IsLocalization.map_units L (⟨s, hs'⟩ : 𝔭.asIdeal.primeCompl)))
      have hfx : hV.fromSpec.base 𝔭 = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have hspec : hV.fromSpec.base q ⤳ x := by
        rw [← hfx]
        apply ((PrimeSpectrum.le_iff_specializes q 𝔭).mp hq𝔭).map hV.fromSpec.base.hom.continuous
      have hqx : q = 𝔭 := by
        apply hV.fromSpec.isOpenEmbedding.injective
        rw [hmax _ hspec, hfx]
      apply le_antisymm (IsLocalRing.le_maximalIdeal hQ.ne_top)
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro s hs
      have hs' : s ∈ q.asIdeal := by
        rw [hqx]
        apply hs
      refine hs'
    have hmax0 : IsLocalRing.maximalIdeal L = ⊥ := by
      rw [eq_bot_iff]
      intro m hm
      have : m ∈ nilradical L := by
        rw [nilradical_eq_sInf, Submodule.mem_sInf]
        intro J hJ
        rw [huniq J hJ]
        apply hm
      rw [mem_nilradical] at this
      apply this.eq_zero
    have : algebraMap (X.presheaf.obj (op V)) L d = 0 := by
      rw [← Ideal.mem_bot, ← hmax0, ← Localization.AtPrime.map_eq_maximalIdeal]
      apply Ideal.mem_map_of_mem _ hd
    obtain ⟨c, hc⟩ := (IsLocalization.map_eq_zero_iff 𝔭.asIdeal.primeCompl L d).mp this
    refine ⟨c, hc⟩
  constructor
  constructor
  ·
    intro s
    rw [isUnit_iff_ne_zero]
    intro h
    apply s.property ((hmem s.val).mpr h)
  ·
    intro z
    obtain ⟨a, r, c, hc, hr, e⟩ := (RingHom.surjectiveOnStalks_iff_forall_maximal'.mp hsos) ⊥ Ideal.bot_isMaximal z
    have hc0 : c ≠ 0 := by
      intro h
      apply hc
      rw [h]
      apply Submodule.zero_mem
    have hr𝔭 : r ∉ 𝔭.asIdeal := by
      intro h
      apply hr
      rw [(hmem r).mp h]
      apply Submodule.zero_mem
    refine ⟨(a, ⟨r, hr𝔭⟩), ?_⟩
    change z * algebraMap (X.presheaf.obj (op V)) F r = algebraMap (X.presheaf.obj (op V)) F a
    have e' : c * (algebraMap (X.presheaf.obj (op V)) F r * z) = c * algebraMap (X.presheaf.obj (op V)) F a := by
      rwa [mul_assoc] at e
    have e'' := mul_left_cancel₀ hc0 e'
    rw [mul_comm]
    apply e''
  ·
    intro a b hab
    have : a - b ∈ 𝔭.asIdeal := by
      rw [hmem, map_sub, hab, sub_self]
    obtain ⟨c, hc⟩ := hkill _ this
    refine ⟨c, ?_⟩
    rw [← sub_eq_zero, ← mul_sub, hc]


-- created on 2026-10-20
