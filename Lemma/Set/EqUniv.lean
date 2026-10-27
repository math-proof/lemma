import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean)
-/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsJacobsonRing A]
  (U : Set (PrimeSpectrum A))
  -- given
  (hU : IsOpen U)
  (hne : U.Nonempty)
  (htrans : ∀ P Q : PrimeSpectrum A, P.asIdeal.IsMaximal → Q.asIdeal.IsMaximal → P ∈ U → Q ∈ U) :
  -- imply
  U = Set.univ := by
  -- proof
  classical
  obtain ⟨P, hP⟩ := hne
  obtain ⟨s, hs⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus _).mp (isClosed_compl_iff.mpr hU)
  have hPnot : ¬ (s ⊆ (P.asIdeal : Set A)) := by
    intro h
    have : P ∈ Uᶜ := by
      rw [hs]
      apply (PrimeSpectrum.mem_zeroLocus _ _).mpr h
    apply this hP
  rw [Set.not_subset] at hPnot
  obtain ⟨f, hfs, hfP⟩ := hPnot
  have hnil : f ∈ nilradical A → f ∈ P.asIdeal := by
    intro h
    apply nilradical_le_prime P.asIdeal h
  have hfrad : f ∉ (⊥ : Ideal A).radical := fun h => hfP (hnil h)
  rw [Ideal.radical_eq_jacobson, Ideal.jacobson, Submodule.mem_sInf] at hfrad
  push Not at hfrad
  obtain ⟨M, ⟨-, hM⟩, hfM⟩ := hfrad
  have hMU : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ U := by
    by_contra h
    have h' : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ := h
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    apply hfM (h' hfs)
  apply Set.eq_univ_of_forall
  intro Q
  by_contra hQ
  have hQz : s ⊆ (Q.asIdeal : Set A) := by
    have h' : Q ∈ Uᶜ := hQ
    rw [hs, PrimeSpectrum.mem_zeroLocus] at h'
    apply h'
  obtain ⟨M', hM', hQM'⟩ := Q.asIdeal.exists_le_maximal Q.isPrime.ne_top
  apply (fun hM'c : (⟨M', hM'.isPrime⟩ : PrimeSpectrum A) ∈ Uᶜ =>
    hM'c (htrans ⟨M, hM.isPrime⟩ ⟨M', hM'.isPrime⟩ hM hM' hMU))
  rw [hs, PrimeSpectrum.mem_zeroLocus]
  intro a ha
  apply hQM' (hQz ha)


-- created on 2026-10-20
