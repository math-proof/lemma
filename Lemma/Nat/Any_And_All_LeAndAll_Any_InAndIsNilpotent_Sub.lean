import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
open IntermediateField


attribute [local instance] Ideal.Quotient.field

@[local instance]
instance {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal :=
  I.isMaximal


private lemma exists_eq_apply_single
  [CommRing S] [IsDomain S]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : ι → Type*} [∀ i, CommRing (R i)]
  (f : (∀ i, R i) →+* S) :
-- imply
  ∃ i₀ : ι, f (Pi.single i₀ 1) = 1 ∧ ∀ x, f x = f (Pi.single i₀ (x i₀)) := by
-- proof
  classical
  have hidem : ∀ i, f (Pi.single i 1) = 0 ∨ f (Pi.single i 1) = 1 := fun i => by
    have h : f (Pi.single i 1) * f (Pi.single i 1) = f (Pi.single i 1) := by
      rw [← map_mul, ← Pi.single_mul, mul_one]
    have hmul : f (Pi.single i 1) * (f (Pi.single i 1) - 1) = 0 := by
      rw [mul_sub, mul_one, h, sub_self]
    obtain h0 | h1 := mul_eq_zero.mp hmul
    · refine Or.inl h0
    · refine Or.inr (sub_eq_zero.mp h1)
  have hsum : ∑ i, f (Pi.single i (1 : R i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : _))]
    apply map_one f
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, f (Pi.single i₀ 1) = 1 := by
    by_contra h
    push Not at h
    have : ∑ i, f (Pi.single i (1 : R i)) = 0 :=
      Finset.sum_eq_zero fun i _ => (hidem i).resolve_right (h i)
    rw [this] at hsum
    exact zero_ne_one hsum
  refine ⟨i₀, hi₀, fun x => ?_⟩
  have hx : x = Pi.single i₀ (x i₀) + x * (1 - Pi.single i₀ 1) := by
    ext i
    if hi : i = i₀ then
      subst hi
      simp
    else
      simp [Pi.single_eq_of_ne hi]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi₀, sub_self, mul_zero, add_zero]

private noncomputable def factorHom
  [CommRing S] [IsDomain S]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : ι → Type*} [∀ i, CommRing (R i)]
  (f : (∀ i, R i) →+* S) :
  R (exists_eq_apply_single f).choose →+* S where
  toFun := fun r => f (Pi.single (exists_eq_apply_single f).choose r)
  map_one' := by
    apply (exists_eq_apply_single f).choose_spec.1
  map_mul' := by
    intro a b
    rw [← map_mul, ← Pi.single_mul]
  map_zero' := by
    rw [Pi.single_zero, map_zero]
  map_add' := by
    intro a b
    rw [← map_add, ← Pi.single_add]

private lemma factorHom_apply
  [CommRing S] [IsDomain S]
  {ι : Type u} [Fintype ι] [DecidableEq ι]
  {R : ι → Type*} [∀ i, CommRing (R i)]
  (f : (∀ i, R i) →+* S)
  (x : ∀ i, R i) :
-- imply
  factorHom f (x (exists_eq_apply_single f).choose) = f x :=
  ((exists_eq_apply_single f).choose_spec.2 x).symm

private lemma isSeparable_apply_of_etale
  {k : Type u} [Field k]
  {S : Type v} [CommRing S] [Algebra k S] [Algebra.Etale k S]
  {F : Type w} [Field F] [Algebra k F]
  (ψ : S →ₐ[k] F)
  (s : S) :
-- imply
  IsSeparable k (ψ s) := by
-- proof
  classical
  obtain ⟨I, hI, L, hL, hLa, e, hsep⟩ := (Algebra.Etale.iff_exists_algEquiv_prod k S).mp inferInstance
  let _ := hI
  let _ : Fintype I := Fintype.ofFinite I
  let f : (∀ i, L i) →+* F := (ψ.comp (e.symm : (∀ i, L i) →ₐ[k] S)).toRingHom
  let i₀ := (exists_eq_apply_single f).choose
  let _ : Algebra.IsSeparable k (L i₀) := (hsep i₀).2
  let g : L i₀ →ₐ[k] F :=
    AlgHom.mk (factorHom f) (fun r => by
      have h1 : factorHom f ((algebraMap k (∀ i, L i) r) i₀) = f (algebraMap k _ r) :=
        factorHom_apply f _
      rw [Pi.algebraMap_apply] at h1
      show factorHom f (algebraMap k (L i₀) r) = _
      rw [h1]
      show ψ (e.symm (algebraMap k _ r)) = _
      rw [AlgEquiv.commutes, AlgHom.commutes])
  have hψ : ψ s = g ((e s) i₀) := by
    show ψ s = factorHom f ((e s) i₀)
    rw [factorHom_apply]
    show ψ s = ψ (e.symm (e s))
    rw [AlgEquiv.symm_apply_apply]
  rw [hψ]
  show (minpoly k (g ((e s) i₀))).Separable
  rw [minpoly.algHom_eq g g.toRingHom.injective]
  apply Algebra.IsSeparable.isSeparable k _

private abbrev Ared (A : Type v) [CommRing A] : Type v := A ⧸ nilradical A

private instance {A : Type v} [CommRing A] : IsReduced (Ared A) :=
  (Ideal.isRadical_iff_quotient_reduced _).mp (Ideal.radical_isRadical ⊥)

private abbrev Fi (A : Type v) [CommRing A] (I : MaximalSpectrum (Ared A)) : Type v :=
  Ared A ⧸ I.asIdeal

private lemma isArtinianRing_Ared
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  IsArtinianRing (Ared A) := by
-- proof
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  infer_instance

private noncomputable def piEquiv
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
  Ared A ≃ₐ[k] (∀ I : MaximalSpectrum (Ared A), Fi A I) :=
  let _ : IsArtinianRing (Ared A) := isArtinianRing_Ared (k := k) (A := A)
  (IsArtinianRing.equivPi (Ared A)).restrictScalars k

private noncomputable def Ebar
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
  Subalgebra k (Ared A) :=
  (Subalgebra.pi Set.univ fun I : MaximalSpectrum (Ared A) =>
    (separableClosure k (Fi A I)).toSubalgebra).comap
    (piEquiv (k := k) (A := A) : Ared A →ₐ[k] ∀ I, Fi A I)

private lemma mem_Ebar
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A]
  {x : Ared A} :
-- imply
  x ∈ Ebar (k := k) (A := A) ↔ ∀ I, IsSeparable k (piEquiv (k := k) (A := A) x I) := by
-- proof
  simp [Ebar, Subalgebra.mem_pi, mem_separableClosure_iff]

private noncomputable def EbarEquiv
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
  Ebar (k := k) (A := A) ≃ₐ[k] (∀ I : MaximalSpectrum (Ared A), separableClosure k (Fi A I)) where
  toFun := fun x => fun I => ⟨piEquiv (k := k) (A := A) x I,
    (mem_separableClosure_iff).mpr ((mem_Ebar (k := k) (A := A)).mp x.2 I)⟩
  invFun := fun y => ⟨(piEquiv (k := k) (A := A)).symm (fun I => (y I : Fi A I)),
    (mem_Ebar (k := k) (A := A)).mpr fun I => by
    rw [AlgEquiv.apply_symm_apply]
    apply (mem_separableClosure_iff).mp (y I).2⟩
  left_inv := by
    intro x
    ext
    simp
  right_inv := by
    intro y
    ext I
    simp
  map_mul' := by
    intro x y
    ext I
    simp
  map_add' := by
    intro x y
    ext I
    simp
  commutes' := by
    intro r
    ext I
    simp [Pi.algebraMap_apply]

private lemma etale_Ebar
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  Algebra.Etale k (Ebar (k := k) (A := A)) := by
-- proof
  let _ : IsArtinianRing (Ared A) := isArtinianRing_Ared (k := k)
  refine (Algebra.Etale.iff_exists_algEquiv_prod k (Ebar (k := k) (A := A))).mpr
    ⟨MaximalSpectrum (Ared A), inferInstance, fun I => separableClosure k (Fi A I), inferInstance, inferInstance,
      EbarEquiv (k := k) (A := A), fun I => ⟨inferInstance, inferInstance⟩⟩

private noncomputable abbrev red
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] :
  A →ₐ[k] Ared A :=
  Ideal.Quotient.mkₐ k (nilradical A)

private lemma red_surjective
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] :
-- imply
  Function.Surjective (red (k := k) (A := A)) :=
  Ideal.Quotient.mkₐ_surjective k _

private lemma isNilpotent_nilradical
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  IsNilpotent (nilradical A) := by
-- proof
  let _ : IsArtinianRing A := IsArtinianRing.of_finite k A
  apply IsArtinianRing.isNilpotent_nilradical

private lemma isNilpotent_ker_red
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  IsNilpotent (RingHom.ker (red (k := k) (A := A) : A →+* Ared A)) := by
-- proof
  have : RingHom.ker (red (k := k) (A := A) : A →+* Ared A) = nilradical A :=
    Ideal.Quotient.mkₐ_ker k _
  rw [this]
  apply isNilpotent_nilradical (k := k)

private noncomputable def lift
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
  Ebar (k := k) (A := A) →ₐ[k] A :=
  let _ := etale_Ebar (k := k) (A := A)
  Algebra.FormallySmooth.liftOfSurjective (Ebar (k := k) (A := A)).val (red (k := k))
    (red_surjective (k := k)) (isNilpotent_ker_red (k := k))

private lemma red_lift
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A]
  (x : Ebar (k := k) (A := A)) :
-- imply
  red (k := k) (lift (k := k) x) = (x : Ared A) := by
-- proof
  let _ := etale_Ebar (k := k) (A := A)
  apply Algebra.FormallySmooth.liftOfSurjective_apply (Ebar (k := k) (A := A)).val (red (k := k))
    (red_surjective (k := k)) (isNilpotent_ker_red (k := k)) x

private lemma lift_injective
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  Function.Injective (lift (k := k) (A := A)) := by
-- proof
  intro x y h
  apply Subtype.ext
  rw [← red_lift (k := k) x, ← red_lift (k := k) y, h]

private noncomputable def Psub
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
  Subalgebra k A :=
  (lift (k := k) (A := A)).range

private lemma etale_P
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  Algebra.Etale k (Psub (k := k) (A := A)) := by
-- proof
  let _ : IsArtinianRing (Ared A) := isArtinianRing_Ared (k := k)
  let e : Psub (k := k) (A := A) ≃ₐ[k] Ebar (k := k) (A := A) :=
    (AlgEquiv.ofInjective (lift (k := k)) (lift_injective (k := k))).symm
  refine (Algebra.Etale.iff_exists_algEquiv_prod k (Psub (k := k) (A := A))).mpr
    ⟨MaximalSpectrum (Ared A), inferInstance, fun I => separableClosure k (Fi A I), inferInstance, inferInstance,
      e.trans (EbarEquiv (k := k) (A := A)), fun I => ⟨inferInstance, inferInstance⟩⟩

private lemma red_mem_Ebar
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A]
  (S : Subalgebra k A) [Algebra.Etale k S]
  (s : S) :
-- imply
  red (k := k) (s : A) ∈ Ebar (k := k) (A := A) := by
-- proof
  rw [mem_Ebar]
  intro I
  let ψ : S →ₐ[k] Fi A I :=
    (Pi.evalAlgHom k (fun J => Fi A J) I).comp
      ((piEquiv (k := k) (A := A) : Ared A →ₐ[k] ∀ J, Fi A J).comp ((red (k := k)).comp S.val))
  apply isSeparable_apply_of_etale (k := k) ψ s

private lemma le_P
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A]
  {S : Subalgebra k A}
-- given
  (hS : Algebra.Etale k S) :
-- imply
  S ≤ Psub (k := k) (A := A) := by
-- proof
  intro s hs
  let _ : Algebra.Etale k S := hS
  let ρ : S →ₐ[k] Ebar (k := k) (A := A) :=
    ((red (k := k)).comp S.val).codRestrict (Ebar (k := k)) (fun x => red_mem_Ebar (k := k) S x)
  let φ : S →ₐ[k] A := (lift (k := k)).comp ρ
  have hφ : S.val = φ := by
    refine Algebra.FormallyUnramified.ext (nilradical A) (isNilpotent_nilradical (k := k)) fun x => ?_
    show red (k := k) (x : A) = red (k := k) (lift (k := k) (ρ x))
    rw [red_lift]
    rfl
  have : (⟨s, hs⟩ : S).val = φ ⟨s, hs⟩ := by
    rw [← hφ]
    rfl
  rw [show s = φ ⟨s, hs⟩ from this]
  refine ⟨ρ ⟨s, hs⟩, rfl⟩

private lemma exists_pow_sub_isNilpotent
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A]
  (x : A) :
-- imply
  ∃ (n : ℕ) (y : A), y ∈ Psub (k := k) (A := A) ∧ IsNilpotent (x ^ ringExpChar k ^ n - y) := by
-- proof
  classical
  let _ : IsArtinianRing (Ared A) := isArtinianRing_Ared (k := k)
  let _ : Fintype (MaximalSpectrum (Ared A)) := Fintype.ofFinite _
  let q := ringExpChar k
  have hI : ∀ I : MaximalSpectrum (Ared A), ∃ n : ℕ,
      IsSeparable k ((piEquiv (k := k) (A := A) (red (k := k) x) I) ^ q ^ n) := by
    intro I
    let _ : ExpChar (separableClosure k (Fi A I)) q :=
      expChar_of_injective_algebraMap (algebraMap k _).injective q
    let _ : Algebra.IsAlgebraic k (Fi A I) := Algebra.IsAlgebraic.of_finite k _
    obtain ⟨n, hn⟩ := IsPurelyInseparable.pow_mem (separableClosure k (Fi A I)) q
      (piEquiv (k := k) (A := A) (red (k := k) x) I)
    refine ⟨n, ?_⟩
    obtain ⟨z, hz⟩ := hn
    rw [← hz]
    apply (mem_separableClosure_iff).mp z.2
  choose n hn using hI
  refine ⟨Finset.univ.sup n, ?_⟩
  have hmem : red (k := k) (x ^ q ^ Finset.univ.sup n) ∈ Ebar (k := k) (A := A) := by
    rw [mem_Ebar]
    intro I
    rw [map_pow, map_pow, Pi.pow_apply]
    have hle : n I ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ I)
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hle
    rw [hm, pow_add, pow_mul]
    apply (mem_separableClosure_iff).mp (pow_mem ((mem_separableClosure_iff).mpr (hn I)) _)
  refine ⟨lift (k := k) ⟨_, hmem⟩, ⟨_, rfl⟩, ?_⟩
  have h : red (k := k) (x ^ q ^ Finset.univ.sup n - lift (k := k) ⟨_, hmem⟩) = 0 := by
    rw [map_sub, red_lift, sub_self]
  have h' : Ideal.Quotient.mk (nilradical A) (x ^ q ^ Finset.univ.sup n - lift (k := k) ⟨_, hmem⟩) = 0 := h
  rw [← mem_nilradical]
  apply Ideal.Quotient.eq_zero_iff_mem.mp h'


/--
[Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_subalgebra_etale_forall_le_forall_exists_pow_expChar_pow_sub_isNilpotent.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Module.Finite k A] :
-- imply
  ∃ P : Subalgebra k A,
    Algebra.Etale k P ∧
    (∀ S : Subalgebra k A, Algebra.Etale k S → S ≤ P) ∧
    (∀ x : A, ∃ (n : ℕ) (y : A), y ∈ P ∧ IsNilpotent (x ^ ringExpChar k ^ n - y)) := by
-- proof
  refine ⟨Psub (k := k) (A := A), etale_P (k := k),
    fun S hS => le_P (S := S) hS,
    fun x => exists_pow_sub_isNilpotent (k := k) x⟩


-- created on 2026-10-13
