import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FaithfullyFlat_pi_and_finitePresentation_pi_of_span_eq_top.lean)
-/
@[path]
private lemma main
  {S : Type} [CommRing S]
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (g : ι → S)
  (C : ι → Type) [∀ i, CommRing (C i)] [∀ i, Algebra S (C i)] [∀ i, Algebra (Localization.Away (g i)) (C i)] [∀ i, IsScalarTower S (Localization.Away (g i)) (C i)]
  -- given
  (hg : Ideal.span (Set.range g) = ⊤)
  (hff : ∀ i, Module.FaithfullyFlat (Localization.Away (g i)) (C i))
  (hfp : ∀ i, Algebra.FinitePresentation (Localization.Away (g i)) (C i)) :
  -- imply
  Module.FaithfullyFlat S (∀ i, C i) ∧ Algebra.FinitePresentation S (∀ i, C i) := by
  -- proof
  classical
  have hflat : ∀ i, Module.Flat S (C i) := fun i =>
    let _ : Module.Flat S (Localization.Away (g i)) := IsLocalization.flat _ (Submonoid.powers (g i))
    let _ : Module.Flat (Localization.Away (g i)) (C i) := (hff i).toFlat
    Module.Flat.trans S (Localization.Away (g i)) (C i)
  have hfpS : ∀ i, Algebra.FinitePresentation S (C i) := fun i =>
    let _ : Algebra.FinitePresentation S (Localization.Away (g i)) :=
      IsLocalization.Away.finitePresentation (g i)
    let _ := hfp i
    Algebra.FinitePresentation.trans S (Localization.Away (g i)) (C i)
  refine ⟨?_, inferInstance⟩
  let _ : Module.Flat S (∀ i, C i) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype S ι C).symm
  refine ⟨fun 𝔪 h𝔪 htop => ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, g i ∉ 𝔪 := by
    by_contra hcon
    push Not at hcon
    apply h𝔪.ne_top
    rw [eq_top_iff, ← hg, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    apply hcon i
  have hdisj : Disjoint (Submonoid.powers (g i) : Set S) (𝔪 : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨n, rfl⟩ hx
    apply hi (h𝔪.isPrime.mem_of_pow_mem n hx)
  have hprime : (𝔪.map (algebraMap S (Localization.Away (g i)))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (g i)) (Localization.Away (g i)) 𝔪 h𝔪.isPrime hdisj
  have hne : (𝔪.map (algebraMap S (Localization.Away (g i)))) • (⊤ : Submodule (Localization.Away (g i)) (C i)) ≠ ⊤ :=
    ((Module.FaithfullyFlat.iff_flat_and_proper_ideal _ _).mp (hff i)).2 _ hprime.ne_top
  rw [Ideal.smul_top_eq_map] at htop
  apply hne
  rw [Ideal.smul_top_eq_map] at ⊢
  rw [Submodule.restrictScalars_eq_top_iff] at htop ⊢
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have h1 : (Ideal.map (algebraMap S (∀ i, C i)) 𝔪).map (Pi.evalRingHom C i) = ⊤ := by
    rw [htop, Ideal.map_top]
  rw [Ideal.map_map] at h1
  convert h1 using 2
  ext s
  rfl


-- created on 2026-10-20
