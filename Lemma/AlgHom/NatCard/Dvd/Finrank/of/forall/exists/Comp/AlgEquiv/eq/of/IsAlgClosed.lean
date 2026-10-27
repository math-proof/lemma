import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_natCard_dvd_finrank_of_forall_exists_comp_algEquiv_eq_of_isAlgClosed.lean)
-/

noncomputable def kerPt
  {k : Type u}
  {B : Type v}
  [Field k]
  [CommRing B]
  [Algebra k B]
  (φ : B →ₐ[k] k) : PrimeSpectrum B :=
  ⟨RingHom.ker φ.toRingHom,
    (RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun c => ⟨algebraMap k B c, by simp⟩)).isPrime⟩

private lemma kerPt_asIdeal
  {k : Type u}
  {B : Type v}
  [Field k]
  [CommRing B]
  [Algebra k B]
  (φ : B →ₐ[k] k) : (kerPt φ).asIdeal = RingHom.ker φ.toRingHom := rfl

private lemma kerPt_injective
  {k : Type u}
  {B : Type v}
  [Field k]
  [CommRing B]
  [Algebra k B] :
  Function.Injective (kerPt (k := k) (B := B)) := by
  intro φ ψ h
  have hker : RingHom.ker φ.toRingHom = RingHom.ker ψ.toRingHom := congrArg PrimeSpectrum.asIdeal h
  apply AlgHom.ext
  intro x
  have h1 : x - algebraMap k B (φ x) ∈ RingHom.ker φ.toRingHom := by simp [RingHom.mem_ker]
  rw [hker] at h1
  simp only [RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, AlgHom.commutes] at h1
  exact (sub_eq_zero.1 h1).symm

private lemma kerPt_surjective
  {k : Type u}
  {B : Type v}
  [Field k]
  [CommRing B]
  [Algebra k B]
  [IsAlgClosed k] [Module.Finite k B] :
  Function.Surjective (kerPt (k := k) (B := B)) := by
  intro p
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  have hmax : p.asIdeal.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal p.asIdeal).1 p.isPrime
  let : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  have : Module.Finite k (B ⧸ p.asIdeal) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k p.asIdeal).toLinearMap (Ideal.Quotient.mkₐ_surjective k p.asIdeal)
  have : Algebra.IsAlgebraic k (B ⧸ p.asIdeal) := Algebra.IsAlgebraic.of_finite k (B ⧸ p.asIdeal)
  let ψ₀ : (B ⧸ p.asIdeal) →ₐ[k] k := IsAlgClosed.lift
  let φ : B →ₐ[k] k := ψ₀.comp (Ideal.Quotient.mkₐ k p.asIdeal)
  refine ⟨φ, ?_⟩
  apply PrimeSpectrum.ext
  rw [kerPt_asIdeal]
  symm
  refine hmax.eq_of_le ?_ ?_
  · exact (RingHom.ker_isMaximal_of_surjective φ.toRingHom (fun c => ⟨algebraMap k B c, by simp⟩)).ne_top
  ·
    intro x hx
    rw [RingHom.mem_ker]
    change ψ₀ (Ideal.Quotient.mkₐ k p.asIdeal x) = 0
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]

private lemma finrank_localization_eq_of_comap
  {k : Type u}
  {B : Type v}
  [Field k]
  [CommRing B]
  [Algebra k B]
  (σ : B ≃ₐ[k] B) (P Q : Ideal B) [P.IsPrime] [Q.IsPrime]
  (h : Q = P.comap (σ : B →+* B)) :
  Module.finrank k (Localization.AtPrime Q) = Module.finrank k (Localization.AtPrime P) := by
  have H : Submonoid.map (σ : B ≃+* B).toMonoidHom Q.primeCompl = P.primeCompl := by
    ext b
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff]
    constructor
    ·
      rintro ⟨a, ha, rfl⟩
      rwa [h, Ideal.mem_comap] at ha
    ·
      intro hb
      refine ⟨(σ : B ≃+* B).symm b, ?_, by simp⟩
      rw [h, Ideal.mem_comap]
      simpa using hb
  let e : (Localization.AtPrime Q) ≃+* (Localization.AtPrime P) :=
    IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime Q) (Localization.AtPrime P) (σ : B ≃+* B) H
  apply (AlgEquiv.ofRingEquiv (f := e) _).toLinearEquiv.finrank_eq
  intro c
  rw [IsScalarTower.algebraMap_apply k B (Localization.AtPrime Q), IsLocalization.ringEquivOfRingEquiv_eq,
    IsScalarTower.algebraMap_apply k B (Localization.AtPrime P)]
  congr 1
  exact σ.commutes c

@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k]
  {B : Type v} [CommRing B] [Algebra k B] [Module.Finite k B]
-- given
  (htrans : ∀ φ ψ : B →ₐ[k] k, ∃ σ : B ≃ₐ[k] B, φ.comp (σ : B →ₐ[k] B) = ψ) :
-- imply
  Nat.card (B →ₐ[k] k) ∣ Module.finrank k B := by
-- proof
  classical
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  have : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  have hbij : Function.Bijective (kerPt (k := k) (B := B)) := ⟨kerPt_injective, kerPt_surjective⟩
  rw [Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, IsArtinianRing.finrank_eq_sum_primeSpectrum B k]
  if hne : Nonempty (PrimeSpectrum B) then
    obtain ⟨p₀⟩ := hne
    have hall : ∀ p : PrimeSpectrum B,
        Module.finrank k (Localization.AtPrime p.asIdeal) = Module.finrank k (Localization.AtPrime p₀.asIdeal) := by
      intro p
      obtain ⟨φ₀, hφ₀⟩ := kerPt_surjective (k := k) p₀
      obtain ⟨φ, hφ⟩ := kerPt_surjective (k := k) p
      obtain ⟨σ, hσ⟩ := htrans φ₀ φ
      apply finrank_localization_eq_of_comap σ
      rw [← hφ₀, ← hφ, kerPt_asIdeal, kerPt_asIdeal, ← hσ, RingHom.comap_ker]
      rfl
    rw [Finset.sum_congr rfl (fun p _ => hall p), Finset.sum_const, Finset.card_univ, smul_eq_mul]
    apply dvd_mul_right
  else
    have : IsEmpty (PrimeSpectrum B) := not_nonempty_iff.1 hne
    simp


-- created on 2026-10-10
