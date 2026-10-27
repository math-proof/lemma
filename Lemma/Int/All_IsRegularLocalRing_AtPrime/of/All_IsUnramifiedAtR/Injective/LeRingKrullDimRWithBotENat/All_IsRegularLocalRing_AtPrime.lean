import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing


/--
[Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsUnramifiedAt_isRegularLocalRing_localization_of_ne_maximalIdeal.lean)
-/
@[path]
private lemma main
  [CommRing R₀] [IsDomain R₀] [IsNoetherianRing R₀] [IsLocalRing R₀]
  [Field K₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
  [CommRing B] [IsNoetherianRing B] [Algebra R₀ B] [Module.Finite R₀ B]
  [CommRing F] [Algebra B F] [Algebra R₀ F] [Algebra K₀ F]
  [IsScalarTower R₀ B F] [IsScalarTower R₀ K₀ F]
  [IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀)) F]
  [IsReduced F]
-- given
  (hR : ∀ (𝔯 : Ideal R₀) [𝔯.IsPrime], 𝔯 ≠ maximalIdeal R₀ →
    IsRegularLocalRing (Localization.AtPrime 𝔯))
  (hdim : ringKrullDim R₀ ≤ (2 : WithBot ENat))
  (hinj : Function.Injective (algebraMap B F))
  (hB : ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → Algebra.IsUnramifiedAt R₀ 𝔭) :
-- imply
  ∀ (𝔭 : Ideal B) [𝔭.IsPrime], ¬ 𝔭.IsMaximal → IsRegularLocalRing (Localization.AtPrime 𝔭) := by
-- proof
  intro 𝔭 _ hnm
  classical
  let 𝔯 : Ideal R₀ := 𝔭.under R₀
  have h𝔯p : 𝔯.IsPrime := Ideal.IsPrime.under R₀ 𝔭
  have : 𝔭.LiesOver 𝔯 := ⟨rfl⟩
  have h𝔯m : 𝔯 ≠ maximalIdeal R₀ := by
    intro h
    apply hnm
    have hmx : (𝔭.comap (algebraMap R₀ B)).IsMaximal := by
      show 𝔯.IsMaximal
      rw [h]
      apply maximalIdeal.isMaximal R₀
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under 𝔭 hmx
  have hAreg : IsRegularLocalRing (Localization.AtPrime 𝔯) := hR 𝔯 h𝔯m
  have hsA : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) : WithBot ENat) = 𝔯.height := by
    rw [hAreg.spanFinrank_maximalIdeal, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔯 (Localization.AtPrime 𝔯)]
  have hsA' : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) : ENat) = 𝔯.height := by
    exact_mod_cast hsA
  have hht : 𝔯.height ≤ 1 := by
    have hlt : 𝔯 < maximalIdeal R₀ := lt_of_le_of_ne (le_maximalIdeal h𝔯p.ne_top) h𝔯m
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    have h2 : ((maximalIdeal R₀).height : WithBot ENat) ≤ 2 := Ideal.height_le_ringKrullDim_of_isPrime.trans hdim
    have h2' : (maximalIdeal R₀).height ≤ 2 := by
      apply WithBot.coe_le_coe.mp
      rw [WithBot.coe_ofNat]
      apply h2
    have h3 : 𝔯.height + 1 ≤ 2 := h1.trans h2'
    cases hq : 𝔯.height using ENat.recTopCoe with
    | top =>
      rw [hq] at h3
      simp at h3
    | coe n =>
      rw [hq] at h3
      norm_cast at h3 ⊢
      omega
  let _ : Algebra (Localization.AtPrime 𝔯) (Localization.AtPrime 𝔭) :=
    Localization.AtPrime.algebraOfLiesOver 𝔯 𝔭
  have hunr : Algebra.IsUnramifiedAt R₀ 𝔭 := hB 𝔭 hnm
  have hmapeq : 𝔯.map (algebraMap R₀ (Localization.AtPrime 𝔭)) = maximalIdeal (Localization.AtPrime 𝔭) :=
    ((Algebra.isUnramifiedAt_iff_map_eq R₀ 𝔯 𝔭).1 hunr).2
  have hmapA : (maximalIdeal (Localization.AtPrime 𝔯)).map
    (algebraMap (Localization.AtPrime 𝔯) (Localization.AtPrime 𝔭)) =
    maximalIdeal (Localization.AtPrime 𝔭) := by
    rw [← hmapeq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have hs : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) ≤
      Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) := by
    rw [← hmapA]
    apply Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (Localization.AtPrime 𝔭) ?_
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 (Localization.AtPrime 𝔭)]
  if h0 : 𝔯 = ⊥ then
    have hq0 : 𝔯.height = 0 := by
      rw [h0]
      apply Ideal.height_bot
    have hA0 : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔯)) = 0 := by
      have h := hsA'
      rw [hq0] at h
      exact_mod_cast h
    have hB0 : Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) = 0 := Nat.le_zero.mp (hA0 ▸ hs)
    rw [hB0, Nat.cast_zero]
    exact_mod_cast (zero_le : (0 : ENat) ≤ 𝔭.height)
  else
    obtain ⟨π, hπ𝔯, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
    have hπ𝔭 : algebraMap R₀ B π ∈ 𝔭 := hπ𝔯
    have hπnzd : algebraMap R₀ B π ∈ nonZeroDivisors B := by
      rw [mem_nonZeroDivisors_iff_right]
      intro b hb
      apply hinj
      rw [map_zero]
      let ξ : nonZeroDivisors R₀ := ⟨π, mem_nonZeroDivisors_of_ne_zero hπ0⟩
      have hu : IsUnit (algebraMap B F (algebraMap R₀ B π)) :=
        IsLocalization.map_units F (⟨algebraMap R₀ B π, Algebra.mem_algebraMapSubmonoid_of_mem ξ⟩ : Algebra.algebraMapSubmonoid B (nonZeroDivisors R₀))
      have h := congrArg (algebraMap B F) hb
      rw [map_mul, map_zero] at h
      apply hu.mul_left_eq_zero.mp h
    have hnotmin : 𝔭 ∉ minimalPrimes B := fun hmin =>
      Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hmin) hπ𝔭 hπnzd
    have h𝔭1 : 1 ≤ 𝔭.height := Order.one_le_iff_ne_zero.mpr fun h => hnotmin (Ideal.height_eq_zero_iff.mp h)
    have hs1 : (Submodule.spanFinrank (maximalIdeal (Localization.AtPrime 𝔭)) : ENat) ≤ 1 := by
      apply ((Nat.cast_le (α := ENat)).mpr hs).trans (hsA'.trans_le hht)
    exact_mod_cast hs1.trans h𝔭1


-- created on 2026-10-13
