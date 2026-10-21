import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isReduced_and_isClosed_or_mem_irreducibleComponents_and_infinite_of_openCover.lean)
-/
@[path]
private lemma main
  (X : (Scheme : Type (u + 1))) [JacobsonSpace X]
  (ι : Type u) (R : ι → Type u) [∀ i, CommRing (R i)]
  (g : ∀ i, Spec (CommRingCat.of (R i)) ⟶ X) (hg : ∀ i, IsOpenImmersion (g i))
  (hcov : ∀ x : X, ∃ i, x ∈ Set.range (g i).base)
  (hred : ∀ i, _root_.IsReduced (R i))
  (hdim : ∀ i (p : Ideal (R i)), p.IsPrime → p.IsMaximal ∨ p ∈ minimalPrimes (R i))
  (hinf : ∀ i (p : Ideal (R i)), p ∈ minimalPrimes (R i) → Set.Infinite {q : PrimeSpectrum (R i) | p ≤ q.asIdeal}) :
    IsReduced X ∧ (∀ z : X, IsClosed ({z} : Set X) ∨ closure ({z} : Set X) ∈ irreducibleComponents X) ∧ (∀ C ∈ irreducibleComponents X, Set.Infinite C) := by
  have hemb : ∀ i, Topology.IsOpenEmbedding (g i).base := fun i => (g i).isOpenEmbedding
  have hspec : ∀ i (p q : PrimeSpectrum (R i)), (g i).base q ⤳ (g i).base p ↔ q.asIdeal ≤ p.asIdeal := by
    intro i p q
    apply ((hemb i).isInducing.specializes_iff).trans ((PrimeSpectrum.le_iff_specializes q p).symm.trans (PrimeSpectrum.asIdeal_le_asIdeal q p).symm)
  have hlift : ∀ i (p : PrimeSpectrum (R i)) (y : X), y ⤳ (g i).base p → ∃ q : PrimeSpectrum (R i), (g i).base q = y ∧ q.asIdeal ≤ p.asIdeal := by
    intro i p y hy
    obtain ⟨q, rfl⟩ : y ∈ Set.range (g i).base := hy.mem_open (hemb i).isOpen_range ⟨p, rfl⟩
    refine ⟨q, rfl, (hspec i p q).mp hy⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
      intro x
      obtain ⟨i, p, rfl⟩ := hcov x
      let _ := hred i
      let _ : IsReduced (Spec (CommRingCat.of (R i))) := inferInstance
      apply isReduced_of_injective ((g i).stalkMap p).hom (asIso ((g i).stalkMap p)).commRingCatIsoToRingEquiv.injective
    apply isReduced_of_isReduced_stalk X
  ·
    intro z
    obtain ⟨i, p, rfl⟩ := hcov z
    cases hdim i p.asIdeal p.isPrime
    ·
      rename_i hmax
      left
      have hcl : p ∈ closedPoints ↥(Spec (CommRingCat.of (R i))) :=
        (PrimeSpectrum.isClosed_singleton_iff_isMaximal p).mpr hmax
      rw [← (hemb i).preimage_closedPoints] at hcl
      apply hcl
    ·
      rename_i hmin
      right
      refine ⟨isIrreducible_singleton.closure, ?_⟩
      intro t ht hzt
      have hη := ht.isGenericPoint_genericPoint_closure
      have hzη : ht.genericPoint ⤳ (g i).base p := by
        rw [specializes_iff_mem_closure, hη.def]
        apply subset_closure (hzt (subset_closure (Set.mem_singleton _)))
      obtain ⟨q, hq, hqp⟩ := hlift i p _ hzη
      have hqp' : q = p := PrimeSpectrum.ext (le_antisymm hqp (hmin.2 ⟨q.isPrime, bot_le⟩ hqp))
      have hηz : ht.genericPoint = (g i).base p := by rw [← hq, hqp']
      calc
        _ ⊆ closure t := subset_closure
        _ = closure {ht.genericPoint} := Eq.symm hη.def
        _ = closure {(g i).base p} := by rw [hηz]
  ·
    intro C hC
    have hCcl : IsClosed C := isClosed_of_mem_irreducibleComponents C hC
    obtain ⟨c, hc⟩ := QuasiSober.sober hC.1 hCcl
    obtain ⟨i, p, hp⟩ := hcov c
    obtain ⟨q₀, hq₀min, hq₀p⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal (R i))) (J := p.asIdeal) bot_le
    let q : PrimeSpectrum (R i) := ⟨q₀, hq₀min.1.1⟩
    have hqc : (g i).base q ⤳ c := by
      rw [← hp]
      apply (hspec i p q).mpr hq₀p
    have hsub : C ⊆ closure {(g i).base q} := by
      rw [← hc.def]
      apply closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hqc)) isClosed_closure
    have hsub' : closure {(g i).base q} ⊆ C := hC.2 isIrreducible_singleton.closure hsub
    have hcq : c ⤳ (g i).base q := by
      rw [specializes_iff_mem_closure, hc.def]
      apply hsub' (subset_closure (Set.mem_singleton _))
    have hpq : p.asIdeal ≤ q.asIdeal := by
      rw [← hp] at hcq
      apply (hspec i q p).mp hcq
    have hpmin : p.asIdeal ∈ minimalPrimes (R i) := by
      have : p.asIdeal = q₀ := le_antisymm hpq hq₀p
      rw [this]
      apply hq₀min
    suffices Set.image (g i).base {q' : PrimeSpectrum (R i) | p.asIdeal ≤ q'.asIdeal} ⊆ C by
      apply Set.Infinite.mono this ((Set.infinite_image_iff (hemb i).injective.injOn).mpr (hinf i p.asIdeal hpmin))
    rintro _ ⟨q', hq', rfl⟩
    have : c ⤳ (g i).base q' := by
      rw [← hp]
      apply (hspec i q' p).mpr hq'
    rw [← hc.def]
    apply specializes_iff_mem_closure.mp this


-- created on 2026-10-20
