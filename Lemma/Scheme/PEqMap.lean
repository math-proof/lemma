import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_algHom_of_perfectField
  (K : Type u) [Field K] [PerfectField K]
  (S : Type u) [CommRing S] [Algebra K S] [Algebra.FiniteType K S]
  (p : Ideal S) (hp : p ≠ ⊤) :
  ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (_ : Algebra.IsSeparable K K') (_ : S →ₐ[K] K'), True := by
  obtain ⟨M, hM, -⟩ := Ideal.exists_le_maximal p hp
  let _ : Field (S ⧸ M) := Ideal.Quotient.field M
  let _ : Algebra.FiniteType K (S ⧸ M) := inferInstance
  let _ : Module.Finite K (S ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (S ⧸ M)
  let _ : Algebra.IsAlgebraic K (S ⧸ M) := Algebra.IsAlgebraic.of_finite K (S ⧸ M)
  let _ : Algebra.IsSeparable K (S ⧸ M) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨S ⧸ M, inferInstance, inferInstance, inferInstance, inferInstance, Ideal.Quotient.mkₐ K M, trivial⟩
private lemma exists_eval_ne_zero
  {K : Type u} [Field K] [Infinite K] {n : ℕ}
  {h : MvPolynomial (Fin n) K} (hh : h ≠ 0) :
  ∃ a : Fin n → K, MvPolynomial.eval a h ≠ 0 := by
  by_contra! H
  exact hh (MvPolynomial.funext fun a => by simpa using H a)
private lemma exists_isMaximal_isSeparable_of_etale
  (K : Type u) [Field K] [Infinite K] (n : ℕ)
  (Sf : Type u) [CommRing Sf] [Algebra K Sf]
  [Algebra (MvPolynomial (Fin n) K) Sf] [IsScalarTower K (MvPolynomial (Fin n) K) Sf]
  [Algebra.Etale (MvPolynomial (Fin n) K) Sf] (Q₀ : Ideal Sf) [Q₀.IsPrime] :
  ∃ (M : Ideal Sf) (_ : M.IsMaximal), FiniteDimensional K (Sf ⧸ M) ∧ Algebra.IsSeparable K (Sf ⧸ M) := by
  classical
  let _ : Module.Flat (MvPolynomial (Fin n) K) Sf := inferInstance
  let _ : Algebra.HasGoingDown (MvPolynomial (Fin n) K) Sf := Algebra.HasGoingDown.of_flat
  have hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf)) :=
    PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
  have hU : IsOpen (Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf))) :=
    hopen.isOpen_range
  let q₀ : PrimeSpectrum (MvPolynomial (Fin n) K) := PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf) ⟨Q₀, ‹_›⟩
  have hq₀ : q₀ ∈ Set.range (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) K) Sf)) := ⟨_, rfl⟩
  obtain ⟨_, ⟨h, rfl⟩, hq₀h, hhU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hq₀ hU
  have hh0 : h ≠ 0 := by
    intro H
    rw [H] at hq₀h
    simp [PrimeSpectrum.basicOpen_zero] at hq₀h
  obtain ⟨a, ha⟩ := exists_eval_ne_zero hh0
  let ev : (MvPolynomial (Fin n) K) →ₐ[K] K := MvPolynomial.aeval a
  have hev : Function.Surjective ev := fun x =>
    ⟨MvPolynomial.C x, by simp [ev]⟩
  let m : Ideal (MvPolynomial (Fin n) K) := RingHom.ker ev
  let hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective ev hev
  have hhm : h ∉ m := by
    change ev h ≠ 0
    simpa [ev, MvPolynomial.aeval_eq_eval, MvPolynomial.coe_aeval_eq_eval] using ha
  have hmD : (⟨m, hm.isPrime⟩ : PrimeSpectrum (MvPolynomial (Fin n) K)) ∈ PrimeSpectrum.basicOpen h := hhm
  obtain ⟨Q, hQ⟩ := hhU hmD
  obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q.asIdeal Q.isPrime.ne_top
  have hmM : m ≤ M.comap (algebraMap (MvPolynomial (Fin n) K) Sf) := by
    have : Q.asIdeal.comap (algebraMap (MvPolynomial (Fin n) K) Sf) = m := by
      simpa [PrimeSpectrum.ext_iff] using hQ
    rw [← this]
    apply Ideal.comap_mono hQM
  let _ : Field (Sf ⧸ M) := Ideal.Quotient.field M
  refine ⟨M, hM, ?_, ?_⟩
  ·
    let _ : Algebra.FiniteType K (MvPolynomial (Fin n) K) := inferInstance
    let _ : Algebra.FiniteType (MvPolynomial (Fin n) K) Sf := inferInstance
    let _ : Algebra.FiniteType K Sf := Algebra.FiniteType.trans (S := (MvPolynomial (Fin n) K)) inferInstance inferInstance
    let _ : Algebra.FiniteType K (Sf ⧸ M) := inferInstance
    apply finite_of_finite_type_of_isJacobsonRing K (Sf ⧸ M)
  ·
    let κ := (MvPolynomial (Fin n) K) ⧸ m
    let _ : Field κ := Ideal.Quotient.field m
    let _ : Algebra κ (Sf ⧸ M) := (Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM).toAlgebra
    let _ : IsScalarTower (MvPolynomial (Fin n) K) κ (Sf ⧸ M) := IsScalarTower.of_algebraMap_eq fun x => by
      change Ideal.Quotient.mk M (algebraMap (MvPolynomial (Fin n) K) Sf x) =
        Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM (Ideal.Quotient.mk m x)
      rw [Ideal.quotientMap_mk]
    let _ : IsScalarTower K κ (Sf ⧸ M) := IsScalarTower.of_algebraMap_eq fun x => by
      change algebraMap Sf (Sf ⧸ M) (algebraMap K Sf x) =
        Ideal.quotientMap M (algebraMap (MvPolynomial (Fin n) K) Sf) hmM (Ideal.Quotient.mk m (algebraMap K (MvPolynomial (Fin n) K) x))
      rw [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K) Sf]
      rfl
    let _ : Algebra.FormallyUnramified (MvPolynomial (Fin n) K) (Sf ⧸ M) :=
      Algebra.FormallyUnramified.comp (MvPolynomial (Fin n) K) Sf (Sf ⧸ M)
    let _ : Algebra.FormallyUnramified κ (Sf ⧸ M) :=
      Algebra.FormallyUnramified.of_restrictScalars (MvPolynomial (Fin n) K) κ (Sf ⧸ M)
    let _ : Algebra.FiniteType (MvPolynomial (Fin n) K) (Sf ⧸ M) := inferInstance
    let _ : Algebra.FiniteType κ (Sf ⧸ M) :=
      Algebra.FiniteType.of_restrictScalars_finiteType (MvPolynomial (Fin n) K) κ (Sf ⧸ M)
    let _ : Algebra.EssFiniteType κ (Sf ⧸ M) := inferInstance
    let _ : Algebra.IsSeparable κ (Sf ⧸ M) := by
      rw [← Algebra.FormallyUnramified.iff_isSeparable κ (Sf ⧸ M)]
      infer_instance
    let e : κ ≃ₐ[K] K := Ideal.quotientKerAlgEquivOfSurjective hev
    let _ : Algebra.IsSeparable K κ :=
      Algebra.IsSeparable.of_algHom K K e.toAlgHom
    apply Algebra.IsSeparable.trans K κ (Sf ⧸ M)
private lemma exists_algHom_of_smooth
  (K : Type u) [Field K]
  (S : Type u) [CommRing S] [Algebra K S] [Algebra.Smooth K S]
  (p : Ideal S) [p.IsPrime] :
  ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (_ : Algebra.IsSeparable K K') (_ : S →ₐ[K] K'), True := by
  classical
  cases finite_or_infinite K with
  | inl hfin =>
    let _ : PerfectField K := inferInstance
    apply exists_algHom_of_perfectField K S p (Ideal.IsPrime.ne_top ‹_›)
  | inr hinf =>
    obtain ⟨f, hfp, n, instMv, htower, hstd⟩ :=
      Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := S) (p := p)
    let _ := instMv
    let _ := htower
    let _ := hstd
    let hp' : (Ideal.map (algebraMap S (Localization.Away f)) p).IsPrime :=
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_›
        (Iff.mpr (Ideal.disjoint_powers_iff_notMem_of_isPrime _) hfp)
    obtain ⟨M, hM, hfinM, hsepM⟩ := exists_isMaximal_isSeparable_of_etale K n
      (Localization.Away f) (Ideal.map (algebraMap S (Localization.Away f)) p)
    let _ : Field (Localization.Away f ⧸ M) := Ideal.Quotient.field M
    exact ⟨Localization.Away f ⧸ M, inferInstance, inferInstance, hfinM, hsepM,
      (Ideal.Quotient.mkₐ K M).comp (IsScalarTower.toAlgHom K S (Localization.Away f)), trivial⟩
/--
[AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_isSeparable_specMap_comp_eq_of_smooth_of_nonempty.lean)
-/
@[path]
private lemma main
  (K : Type u) [Field K] {V : (Scheme : Type (u + 1))} (g : V ⟶ Spec (CommRingCat.of K)) [Smooth g]
  [Nonempty V] :
  ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (_ : Algebra.IsSeparable K K') (P : Spec (CommRingCat.of K') ⟶ V), P ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K K')) := by
  classical
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, -⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (hU.fromSpec ≫ g)
  have hsm : Smooth (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at hsm
  algebraize [ψ.hom]
  obtain ⟨x, -⟩ : ∃ x : Spec (V.presheaf.obj (op U)), hU.fromSpec.base x = v := by
    have : v ∈ Set.range hU.fromSpec.base := by
      rwa [hU.range_fromSpec]
    apply this
  obtain ⟨K', _, _, _, _, χ, -⟩ :=
    exists_algHom_of_smooth K (V.presheaf.obj (op U)) x.asIdeal
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ hU.fromSpec, ?_⟩
  rw [Category.assoc, ← hψ, ← Spec.map_comp]
  congr 1
  ext1
  change χ.toRingHom.comp ψ.hom = algebraMap K K'
  apply χ.comp_algebraMap


-- created on 2026-10-20
