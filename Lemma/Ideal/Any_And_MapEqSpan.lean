import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/--
[Ideal_exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_isIdempotentElem_map_mk_eq_span_of_forall_map_localization_eq.lean)
-/
@[path]
private lemma main
    (P : Type u) [CommRing P] [IsNoetherianRing P] (I J : Ideal P) (hIJ : I ≤ J)
    (hloc : ∀ (𝔫 : Ideal P) [𝔫.IsMaximal], J ≤ 𝔫 →
      Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) J = Ideal.map (algebraMap P (Localization.AtPrime 𝔫)) I) :
    ∃ e : P ⧸ I, IsIdempotentElem e ∧ Ideal.map (Ideal.Quotient.mk I) J = Ideal.span {e} := by
  classical
  set Jb : Ideal (P ⧸ I) := J.map (Ideal.Quotient.mk I) with hJb
  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  have hfg : Jb.FG := IsNoetherian.noetherian Jb
  have hle : Jb ≤ Jb * Jb := by
    refine Ideal.le_of_localization_maximal fun 𝔪 h𝔪 => ?_
    let _ := h𝔪
    set 𝔫 : Ideal P := 𝔪.comap (Ideal.Quotient.mk I) with h𝔫
    let h𝔫max : 𝔫.IsMaximal := Ideal.comap_isMaximal_of_surjective _ hmk
    by_cases hJ𝔫 : J ≤ 𝔫
    ·
      have hzero : Jb.map (algebraMap (P ⧸ I) (Localization.AtPrime 𝔪)) = ⊥ := by
        rw [hJb, Ideal.map_map, ← le_bot_iff, Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, Ideal.mem_bot, RingHom.comp_apply, IsLocalization.map_eq_zero_iff 𝔪.primeCompl]
        have h1 : algebraMap P (Localization.AtPrime 𝔫) x ∈ I.map (algebraMap P (Localization.AtPrime 𝔫)) := by
          rw [← hloc 𝔫 hJ𝔫]
          exact Ideal.mem_map_of_mem _ hx
        obtain ⟨⟨y, s⟩, hys⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔫.primeCompl _).1 h1
        rw [← map_mul] at hys
        obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔫.primeCompl _).1 hys
        have hcs : (c : P) * s ∉ 𝔫 := 𝔫.primeCompl.mul_mem c.2 s.2
        refine ⟨⟨Ideal.Quotient.mk I ((c : P) * s), fun h => hcs ((Ideal.mem_comap).2 h)⟩, ?_⟩
        change Ideal.Quotient.mk I ((c : P) * s) * Ideal.Quotient.mk I x = 0
        rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, show (c : P) * s * x = c * (x * s) by ring]
        change (c : P) * (x * ((y, s) : _ × _).2) ∈ I
        rw [hc]
        exact I.mul_mem_left _ y.2
      rw [hzero]
      exact bot_le
    ·
      have hJb𝔪 : ¬ Jb ≤ 𝔪 := fun h => hJ𝔫 (Ideal.le_comap_map.trans (Ideal.comap_mono h))
      obtain ⟨u, huJ, hu𝔪⟩ := Set.not_subset.1 hJb𝔪
      have hu2 : u * u ∉ 𝔪 := fun h => (h𝔪.isPrime.mem_or_mem h).elim hu𝔪 hu𝔪
      have htop : (Jb * Jb).map (algebraMap (P ⧸ I) (Localization.AtPrime 𝔪)) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.mul_mem_mul huJ huJ))
          (IsLocalization.map_units _ (⟨u * u, hu2⟩ : 𝔪.primeCompl))
      rw [htop]
      exact le_top
  have hidem : IsIdempotentElem Jb := le_antisymm Ideal.mul_le_left hle
  obtain ⟨e, he, hJe⟩ := (Ideal.isIdempotentElem_iff_of_fg Jb hfg).1 hidem
  exact ⟨e, he, hJe⟩

-- created on 2026-10-20
