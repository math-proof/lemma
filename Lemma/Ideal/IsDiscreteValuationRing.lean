import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  (p : Ideal R) [p.IsPrime]
  -- given
  (hp : p.height = 1) :
  -- imply
  IsDiscreteValuationRing (Localization.AtPrime p) := by
  -- proof
  let hIC : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 (Localization.AtPrime p) :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hprime_max : ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have h3 : IsIntegrallyClosed (Localization.AtPrime p) ∧
      ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    ⟨hIC, fun P hPne hPprime => IsLocalRing.eq_maximalIdeal (hprime_max P hPne hPprime)⟩
  let hPIR : IsPrincipalIdealRing (Localization.AtPrime p) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime p)).out 4 1).mp h3
  have hp_ne : p ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal R).height = 0 := Ideal.height_bot
    rw [h0] at hp
    apply zero_ne_one hp
  have hne_bot : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
    obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp_ne
    intro hbot
    have hxm : algebraMap R (Localization.AtPrime p) x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      apply Ideal.mem_map_of_mem _ hxp
    rw [hbot, Ideal.mem_bot] at hxm
    apply hx0 ((IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
      (by rw [hxm, map_zero]))
  refine { hPIR with not_a_field' := hne_bot }


-- created on 2026-10-20
