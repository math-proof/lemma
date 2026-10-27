import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000


private lemma includeRight_surjective_of_residueField
  (Rp Sq : Type u) [CommRing Rp] [IsLocalRing Rp] [CommRing Sq] [Algebra Rp Sq] :
-- imply
  Function.Surjective (Algebra.TensorProduct.includeRight :
    Sq →ₐ[Rp] IsLocalRing.ResidueField Rp ⊗[Rp] Sq) := by
-- proof
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul c t =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a • t, ?_⟩
    rw [map_smul, Algebra.TensorProduct.includeRight_apply, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
    rfl
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    refine ⟨s + t, ?_⟩
    apply map_add


/--
[Algebra_isSmoothAt_of_isSmoothAt_fiber](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_isSmoothAt_of_isSmoothAt_fiber.lean)
-/
@[path]
private lemma main
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra.FinitePresentation R S]
  {p : Ideal R} [p.IsPrime]
  {q : Ideal S} [q.IsPrime] [q.LiesOver p]
  {Q : Ideal (p.Fiber S)} [Q.IsPrime]
-- given
  (hQ : Q.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom = q)
  [Algebra.IsSmoothAt p.ResidueField Q] :
-- imply
  Algebra.IsSmoothAt R q := by
-- proof
  classical
  let Rp := Localization.AtPrime p
  let Sp := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let Sq := Localization.AtPrime q
  let _ : Algebra Rp Sq := Localization.AtPrime.algebraOfLiesOver p q
  have hle : Algebra.algebraMapSubmonoid S p.primeCompl ≤ q.primeCompl := by
    intro _ hmem h
    obtain ⟨x, hx, rfl⟩ := hmem
    apply hx
    have : x ∈ q.under R := Ideal.mem_comap.mpr h
    rwa [← Ideal.over_def q p] at this
  let f : Sp →ₐ[S] Sq := IsLocalization.liftAlgHom (M := Algebra.algebraMapSubmonoid S p.primeCompl)
    (f := Algebra.ofId S Sq) (fun y => IsLocalization.map_units Sq ⟨y.1, hle y.2⟩)
  let _ : Algebra Sp Sq := f.toRingHom.toAlgebra
  have : IsScalarTower S Sp Sq := IsScalarTower.of_algebraMap_eq fun s => (f.commutes s).symm
  have : IsScalarTower R Sp Sq := IsScalarTower.to₁₃₄ R S Sp Sq
  have : IsLocalization (Algebra.algebraMapSubmonoid Sp q.primeCompl) Sq :=
    IsLocalization.isLocalization_of_submonoid_le Sp Sq
      (Algebra.algebraMapSubmonoid S p.primeCompl) q.primeCompl hle
  have : Algebra.IsPushout R Rp S Sp := (Algebra.isPushout_of_isLocalization p.primeCompl Rp S Sp).symm
  have : Algebra.FinitePresentation Rp Sp :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv R Rp S Sp)
  let _ : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  let T : Type u := (p.Fiber S) ⊗[S] Sq
  let M : Submonoid (p.Fiber S) := Algebra.algebraMapSubmonoid (p.Fiber S) q.primeCompl
  have : IsLocalization M T := IsLocalization.tensor Sq q.primeCompl
  have halg : ∀ s : S, algebraMap S (p.Fiber S) s =
      (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S) s :=
    fun _ => rfl
  have hMQ : Disjoint (M : Set (p.Fiber S)) (Q : Set (p.Fiber S)) := by
    rw [Set.disjoint_left]
    intro _ hmem hsQ
    obtain ⟨s, hs, rfl⟩ := hmem
    apply hs
    rwa [← hQ]
  have hQT : (Q.map (algebraMap (p.Fiber S) T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M T Q ‹_› hMQ
  have : Nontrivial T := nontrivial_of_ne 0 1 fun h =>
    hQT.ne_top ((Ideal.eq_top_iff_one _).mpr (by rw [← h]; exact Ideal.zero_mem _))
  let κ := p.ResidueField
  let e : κ ⊗[R] S ≃ₐ[S] S ⊗[R] κ :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R κ S).toRingEquiv) (fun _ => rfl)
  let e₁ : T ≃ₐ[S] Sq ⊗[S] (κ ⊗[R] S) := Algebra.TensorProduct.comm S (κ ⊗[R] S) Sq
  let e₂ : Sq ⊗[S] (κ ⊗[R] S) ≃ₐ[S] Sq ⊗[S] (S ⊗[R] κ) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : Sq ≃ₐ[S] Sq) e
  let e₃ : Sq ⊗[S] (S ⊗[R] κ) ≃ₐ[S] Sq ⊗[R] κ := Algebra.TensorProduct.cancelBaseChange R S S Sq κ
  let e₄ : Sq ⊗[R] κ ≃ₐ[R] κ ⊗[R] Sq := Algebra.TensorProduct.comm R Sq κ
  let e₅ : κ ⊗[R] Sq ≃ₐ[R] κ ⊗[Rp] Sq := Algebra.TensorProduct.equivOfCompatibleSMul Rp R R κ Sq
  let e' : T ≃ₐ[R] κ ⊗[Rp] Sq :=
    (((e₁.trans e₂).trans e₃).restrictScalars R).trans (e₄.trans e₅)
  have : IsLocalRing T := by
    refine IsLocalRing.of_surjective' (e'.symm.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Rp) (A := κ) (B := Sq)).toRingHom) ?_
    apply e'.symm.surjective.comp (includeRight_surjective_of_residueField Rp Sq)
  let P : Ideal (p.Fiber S) := (IsLocalRing.maximalIdeal T).comap (algebraMap (p.Fiber S) T)
  have hP : P.IsPrime := Ideal.comap_isPrime _ _
  have hQP : Q ≤ P :=
    le_trans Ideal.le_comap_map (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQT.ne_top))
  have hMP : Disjoint (M : Set (p.Fiber S)) (P : Set (p.Fiber S)) := by
    rw [Set.disjoint_left]
    intro y hy hyP
    exact (IsLocalRing.mem_maximalIdeal _).mp hyP (IsLocalization.map_units T ⟨y, hy⟩)
  have hPq : P.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] p.Fiber S).toRingHom = q := by
    apply le_antisymm
    ·
      intro s hs
      by_contra hsq
      exact Set.disjoint_left.mp hMP ⟨s, hsq, rfl⟩ hs
    ·
      rw [← hQ]
      exact Ideal.comap_mono hQP
  have hPQ : P = Q := by
    apply congrArg PrimeSpectrum.asIdeal ((PrimeSpectrum.preimageEquivFiber R S ⟨p, ‹_›⟩).symm.injective
      (a₁ := ⟨P, hP⟩) (a₂ := ⟨Q, ‹_›⟩) (Subtype.ext (PrimeSpectrum.ext (hPq.trans hQ.symm))))
  have : IsLocalization.AtPrime T Q := by
    refine IsLocalization.of_le M Q.primeCompl (fun y hy hyQ => Set.disjoint_left.mp hMQ hy hyQ) ?_
    intro y hy
    by_contra h
    apply hy
    rw [← hPQ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr h
  have : IsScalarTower κ (p.Fiber S) T := inferInstance
  let eQ : Localization.AtPrime Q ≃ₐ[p.Fiber S] T :=
    IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) T
  have hsm : Algebra.FormallySmooth κ (Localization.AtPrime Q) := ‹Algebra.IsSmoothAt κ Q›
  have : Algebra.FormallySmooth κ T :=
    @Algebra.FormallySmooth.of_equiv κ _ (Localization.AtPrime Q) T _ _ _ _ hsm (eQ.restrictScalars κ)
  have hcomm : ((e' : T →ₐ[R] κ ⊗[Rp] Sq).comp (IsScalarTower.toAlgHom R κ T)).comp
    (IsScalarTower.toAlgHom R R κ) =
      (IsScalarTower.toAlgHom R κ (κ ⊗[Rp] Sq)).comp (IsScalarTower.toAlgHom R R κ) := by
    ext
  have hcomm' : (e' : T →ₐ[R] κ ⊗[Rp] Sq).comp (IsScalarTower.toAlgHom R κ T) =
      IsScalarTower.toAlgHom R κ (κ ⊗[Rp] Sq) :=
    Ideal.ResidueField.algHom_ext hcomm
  let e'' : T ≃ₐ[κ] κ ⊗[Rp] Sq :=
    AlgEquiv.ofRingEquiv (f := e'.toRingEquiv) (fun c => congrArg (fun g => g c) hcomm')
  have : Algebra.FormallySmooth (IsLocalRing.ResidueField Rp) (IsLocalRing.ResidueField Rp ⊗[Rp] Sq) :=
    @Algebra.FormallySmooth.of_equiv κ _ T (κ ⊗[Rp] Sq) _ _ _ _ ‹Algebra.FormallySmooth κ T› e''
  have : IsScalarTower Rp Sp Sq := IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext p.primeCompl (by rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq R Rp Sp, ← IsScalarTower.algebraMap_eq R Sp Sq, ← IsScalarTower.algebraMap_eq R Rp Sq]))
  have : Algebra.FormallySmooth Rp Sq :=
    Algebra.FormallySmooth.of_formallySmooth_residueField_tensor
      (Algebra.algebraMapSubmonoid Sp q.primeCompl)
  apply Algebra.FormallySmooth.comp R Rp Sq


-- created on 2026-10-13
