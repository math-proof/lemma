import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma mem_range_algebraMap_of_prime_of_forall_prime_exists_denominator
  [CommRing S] [CommRing K] [IsDomain K] [Algebra S K]
  (hinj : Function.Injective (algebraMap S K))
  (ϖ : S) (hϖ : (Ideal.span {ϖ} : Ideal S).IsPrime) (hϖ0 : ϖ ≠ 0) (f : K)
  (h1 : ∃ a b : S, b ∉ Ideal.span {ϖ} ∧ f * algebraMap S K b = algebraMap S K a)
  (h2 : ∀ 𝔮 : Ideal S, 𝔮.IsPrime → ϖ ∉ 𝔮 → ∃ s a : S, s ∉ 𝔮 ∧ f * algebraMap S K s = algebraMap S K a) :
  f ∈ Set.range (algebraMap S K) := by
  classical
  let D : Ideal S :=
    { carrier := {s | ∃ a : S, f * algebraMap S K s = algebraMap S K a}
      add_mem' := by
        rintro s t ⟨a, ha⟩ ⟨a', ha'⟩
        exact ⟨a + a', by rw [map_add, mul_add, ha, ha', map_add]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c s ⟨a, ha⟩
        exact ⟨c * a, by rw [smul_eq_mul, map_mul, mul_left_comm, ha, map_mul]⟩ }
  have hD : ∀ s : S, s ∈ D ↔ ∃ a : S, f * algebraMap S K s = algebraMap S K a := fun s => Iff.rfl
  have hrad : ϖ ∈ D.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro J ⟨hDJ, hJ⟩
    by_contra hϖJ
    obtain ⟨s, a, hs, hsa⟩ := h2 J hJ hϖJ
    apply hs (hDJ (Iff.mpr (hD s) ⟨a, hsa⟩))
  rw [Ideal.mem_radical_iff] at hrad
  obtain ⟨n, hn⟩ := hrad
  obtain ⟨a₀, b, hb, hab⟩ := h1
  have hϖK : algebraMap S K ϖ ≠ 0 := fun h => hϖ0 (hinj (by rw [h, map_zero]))
  have peel : ∀ m : ℕ, ϖ ^ m ∈ D → (1 : S) ∈ D := by
    intro m
    induction m with
    | zero =>
      intro h
      simpa using h
    | succ m ih =>
      rintro ⟨a', ha'⟩
      have h3 : a' * b = ϖ ^ (m + 1) * a₀ := by
        apply hinj
        rw [map_mul, map_mul, ← ha', ← hab]
        ring
      have h4 : a' * b ∈ (Ideal.span {ϖ} : Ideal S) := by
        rw [h3, pow_succ']
        apply Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ))
      have h5 : a' ∈ (Ideal.span {ϖ} : Ideal S) := (hϖ.mem_or_mem h4).resolve_right hb
      rw [Ideal.mem_span_singleton'] at h5
      obtain ⟨a'', ha''⟩ := h5
      apply ih
      refine ⟨a'', ?_⟩
      apply mul_left_cancel₀ hϖK
      calc
        _ = f * algebraMap S K (ϖ ^ (m + 1)) := by
          rw [map_pow, map_pow, pow_succ]
          ring
        _ = algebraMap S K a' := ha'
        _ = algebraMap S K (a'' * ϖ) := by rw [ha'']
        _ = algebraMap S K ϖ * algebraMap S K a'' := by rw [map_mul, mul_comm]
  obtain ⟨a, ha⟩ := peel n hn
  exact ⟨a, by rw [← ha, map_one, mul_one]⟩
private lemma primeIdealOf_fromSpec
  {X : Scheme} {U : X.Opens} (hU : IsAffineOpen U)
  (y : PrimeSpectrum (X.presheaf.obj (op U))) (h : hU.fromSpec.base y ∈ U) :
  hU.primeIdealOf ⟨hU.fromSpec.base y, h⟩ = y := by
  have h1 : (⟨hU.fromSpec.base y, h⟩ : U) = hU.isoSpec.inv.base y := by
    apply Subtype.ext
    change hU.fromSpec.base y = _
    rw [← hU.isoSpec_inv_ι]
    rfl
  change hU.isoSpec.hom.base _ = y
  rw [h1]
  apply congrArg (fun f : Spec (X.presheaf.obj (op U)) ⟶ Spec (X.presheaf.obj (op U)) => f.base y) hU.isoSpec.inv_hom_id
/--
[AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_mem_range_algebraMap_stalk_functionField_of_forall_specializes_isUnit_of_exists_mul_eq.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] {X : (Scheme : Type (u + 1))} [IsIntegral X] (c : X ⟶ Spec (CommRingCat.of R)) (r : R) (x : X)
  (hprime : (Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))}).IsPrime)
  (hne : (X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) ≠ 0)
  (f : X.functionField)
  (h1 : ∃ a b : X.presheaf.stalk x, b ∉ Ideal.span {(X.presheaf.germ ⊤ x trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))} ∧ f * algebraMap (X.presheaf.stalk x) X.functionField b = algebraMap (X.presheaf.stalk x) X.functionField a)
  (h2 : ∀ P : X, P ⤳ x → IsUnit ((X.presheaf.germ ⊤ P trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))) → f ∈ Set.range (algebraMap (X.presheaf.stalk P) X.functionField)) :
  f ∈ Set.range (algebraMap (X.presheaf.stalk x) X.functionField) := by
  classical
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  obtain ⟨xU, rfl⟩ : ∃ xU : U, (xU : X) = x := ⟨⟨x, hxU⟩, rfl⟩
  let _ : Nonempty U := ⟨xU⟩
  let _ : IsFractionRing (X.presheaf.obj (op U)) X.functionField := functionField_isFractionRing_of_isAffineOpen X U hU
  let _ : IsLocalization.AtPrime (X.presheaf.stalk (xU : X)) (hU.primeIdealOf xU).asIdeal :=
    hU.isLocalization_stalk xU
  let _ : IsScalarTower (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) X.functionField := functionField_isScalarTower X U xU
  set r' : (X.presheaf.obj (op ⊤)) := c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) with hr'
  set rA : (X.presheaf.obj (op U)) := (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom r' with hrA
  have hϖA : algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) rA = (X.presheaf.germ ⊤ (xU : X) trivial).hom r' :=
    TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) (xU : X) xU.2 r'
  refine mem_range_algebraMap_of_prime_of_forall_prime_exists_denominator
    (FaithfulSMul.algebraMap_injective _ _) _ hprime hne f h1 ?_
  intro 𝔮 h𝔮 hϖ𝔮
  let 𝔮A : Ideal (X.presheaf.obj (op U)) := 𝔮.comap (algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)))
  let h𝔮A : 𝔮A.IsPrime := Ideal.comap_isPrime _ 𝔮
  let y : PrimeSpectrum (X.presheaf.obj (op U)) := ⟨𝔮A, h𝔮A⟩
  have hPU : hU.fromSpec.base y ∈ U := by
    have : hU.fromSpec.base y ∈ Set.range hU.fromSpec.base := ⟨y, rfl⟩
    rw [hU.range_fromSpec] at this
    apply this
  obtain ⟨PU, hyP⟩ : ∃ PU : U, hU.primeIdealOf PU = y :=
    ⟨⟨hU.fromSpec.base y, hPU⟩, primeIdealOf_fromSpec hU y hPU⟩
  have hPeq : (PU : X) = hU.fromSpec.base y := by
    rw [← hyP, IsAffineOpen.fromSpec_primeIdealOf]
  let _ : IsLocalization.AtPrime (X.presheaf.stalk (PU : X)) 𝔮A := by
    have h := hU.isLocalization_stalk PU
    rw [hyP] at h
    apply h
  let _ : IsScalarTower (X.presheaf.obj (op U)) (X.presheaf.stalk (PU : X)) X.functionField := functionField_isScalarTower X U PU
  have hPx : (PU : X) ⤳ (xU : X) := by
    have h3 : y ⤳ hU.primeIdealOf xU := by
      rw [← PrimeSpectrum.le_iff_specializes]
      intro a ha
      change algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) a ∈ 𝔮 at ha
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (X.presheaf.stalk (xU : X)) (hU.primeIdealOf xU).asIdeal a]
      apply IsLocalRing.le_maximalIdeal h𝔮.ne_top ha
    have h4 := h3.map hU.fromSpec.base.hom.continuous
    change hU.fromSpec.base y ⤳ hU.fromSpec.base (hU.primeIdealOf xU) at h4
    rwa [IsAffineOpen.fromSpec_primeIdealOf, ← hPeq] at h4
  have hrP : IsUnit ((X.presheaf.germ ⊤ (PU : X) trivial).hom r') := by
    have h5 : (X.presheaf.germ ⊤ (PU : X) trivial).hom r' = algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (PU : X)) rA :=
      (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (le_top : U ≤ ⊤)) (PU : X) PU.2 r').symm
    rw [h5]
    refine IsLocalization.map_units (X.presheaf.stalk (PU : X)) (⟨rA, ?_⟩ : 𝔮A.primeCompl)
    change algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) rA ∉ 𝔮
    rwa [hϖA]
  obtain ⟨g, hg⟩ := h2 (PU : X) hPx hrP
  obtain ⟨⟨t, u⟩, hgu⟩ := IsLocalization.mk'_surjective 𝔮A.primeCompl g
  refine ⟨algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) u, algebraMap (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) t, u.2, ?_⟩
  rw [← IsScalarTower.algebraMap_apply (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) X.functionField (u : (X.presheaf.obj (op U))),
    ← IsScalarTower.algebraMap_apply (X.presheaf.obj (op U)) (X.presheaf.stalk (xU : X)) X.functionField t,
    IsScalarTower.algebraMap_apply (X.presheaf.obj (op U)) (X.presheaf.stalk (PU : X)) X.functionField (u : (X.presheaf.obj (op U))),
    IsScalarTower.algebraMap_apply (X.presheaf.obj (op U)) (X.presheaf.stalk (PU : X)) X.functionField t,
    ← hg, ← hgu, ← map_mul, IsLocalization.mk'_spec]


-- created on 2026-10-20
