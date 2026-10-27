import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isAffineOpen_le_inf_forall_mem_of_finset.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (W : X.Opens) (hW : IsAffineOpen W) (O : X.Opens) (F : Finset X)
  -- given
  (hFW : ∀ x ∈ F, x ∈ W)
  (hFO : ∀ x ∈ F, x ∈ O) :
  -- imply
  ∃ W' : X.Opens, IsAffineOpen W' ∧ W' ≤ W ⊓ O ∧ ∀ x ∈ F, x ∈ W' := by
  -- proof
  classical
  have stepA : ∀ (R : Type u) [CommRing R] (O' : TopologicalSpace.Opens (PrimeSpectrum R)) (F' : Finset (PrimeSpectrum R)), (∀ p ∈ F', p ∈ O') → ∃ a : R, PrimeSpectrum.basicOpen a ≤ O' ∧ ∀ p ∈ F', p ∈ PrimeSpectrum.basicOpen a := by
    intro R _ O' F' hF'
    set Z : Set (PrimeSpectrum R) := (O' : Set (PrimeSpectrum R))ᶜ with hZ
    have hZc : IsClosed Z := O'.isOpen.isClosed_compl
    set I : Ideal R := PrimeSpectrum.vanishingIdeal Z with hI
    have hZI : PrimeSpectrum.zeroLocus (I : Set R) = Z := by
      rw [hI, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZc.closure_eq]
    obtain hF0 | ⟨p₀, hp₀⟩ := F'.eq_empty_or_nonempty
    ·
      refine ⟨0, ?_, by simp [hF0]⟩
      rw [PrimeSpectrum.basicOpen_zero]
      apply bot_le
    have hnot : ¬ ((I : Set R) ⊆ ⋃ p ∈ F', ((fun q : PrimeSpectrum R => q.asIdeal) p : Set R)) := by
      intro hsub
      obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime p₀ p₀ (fun (q : PrimeSpectrum R) _ _ _ => q.isPrime) (s := F') (f := fun q : PrimeSpectrum R => q.asIdeal) (I := I)).mp hsub
      have : p ∈ Z := by
        rw [← hZI]
        apply hle
      apply this (hF' p hp)
    rw [Set.not_subset] at hnot
    obtain ⟨a, haI, ha⟩ := hnot
    simp only [Set.mem_iUnion, not_exists] at ha
    refine ⟨a, fun y hy => ?_, fun p hp => ha p hp⟩
    by_contra hyO
    have hyZ : y ∈ Z := hyO
    rw [← hZI] at hyZ
    apply hy (hyZ haI)
  have hsurj : ∀ x ∈ F, ∃ p : Spec (X.presheaf.obj (op W)), hW.fromSpec p = x := fun x hx => by
    have : x ∈ Set.range ⇑hW.fromSpec := by
      rw [hW.range_fromSpec]
      apply hFW x hx
    apply this
  choose p hp using hsurj
  let F' : Finset (PrimeSpectrum (X.presheaf.obj (op W))) := F.attach.image fun x => p x.1 x.2
  have hF'mem : ∀ q ∈ F', q ∈ (TopologicalSpace.Opens.map hW.fromSpec.base).obj O := by
    intro q hq
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hq
    change hW.fromSpec (p x.1 x.2) ∈ O
    rw [hp]
    apply hFO x.1 x.2
  obtain ⟨a, haO, haF⟩ := stepA (X.presheaf.obj (op W)) ((TopologicalSpace.Opens.map hW.fromSpec.base).obj O) F' hF'mem
  refine ⟨X.basicOpen a, hW.basicOpen a, ?_, ?_⟩
  ·
    intro y hy
    refine ⟨X.basicOpen_le a hy, ?_⟩
    have hyW : y ∈ Set.range ⇑hW.fromSpec := by
      rw [hW.range_fromSpec]
      apply X.basicOpen_le a hy
    obtain ⟨q, rfl⟩ := hyW
    have hq : q ∈ PrimeSpectrum.basicOpen a := by
      rw [← hW.fromSpec_preimage_basicOpen a]
      apply hy
    refine haO hq
  ·
    intro x hx
    have hq : p x hx ∈ PrimeSpectrum.basicOpen a := haF _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
    rw [← hW.fromSpec_preimage_basicOpen a] at hq
    change hW.fromSpec (p x hx) ∈ X.basicOpen a at hq
    rwa [hp] at hq


-- created on 2026-10-20
