import Mathlib
import Lemma.AdicCompletion.Support.Exists

open IsLocalRing AdicCompletion

/--
[AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_exists_ringEquiv_quotient_map_adicCompletion_quotient.lean)
-/
@[path]
private lemma main
-- given
  [CommRing N] [IsNoetherianRing N] {I 𝔭 : Ideal N} :
-- imply
  ∃ (e : RingEquiv (AdicCompletion I N ⧸ 𝔭.map (algebraMap N (AdicCompletion I N)))
      (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭))),
    ∀ x : N, e (Ideal.Quotient.mk _ (algebraMap N (AdicCompletion I N) x)) =
      algebraMap (N ⧸ 𝔭) (AdicCompletion (I.map (Ideal.Quotient.mk 𝔭)) (N ⧸ 𝔭))
        (Ideal.Quotient.mk 𝔭 x) := by
-- proof
  obtain ⟨⟨e, he⟩⟩ := AdicCompletion.exists_ringEquiv_quotient_map_adicCompletion_quotient N I 𝔭
  exact ⟨e, he⟩


-- created on 2026-10-09
