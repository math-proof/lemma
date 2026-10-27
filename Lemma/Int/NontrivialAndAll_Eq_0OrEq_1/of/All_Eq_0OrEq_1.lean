import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


private lemma eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing
  [CommRing S] [IsLocalRing S]
  {e : S}
-- given
  (he : IsIdempotentElem e) :
-- imply
  e = 0 ∨ e = 1 := by
-- proof
  have h0 : e * (1 - e) = 0 := by
    rw [mul_sub, mul_one, he.eq, sub_self]
  obtain hu | hu := IsLocalRing.isUnit_or_isUnit_one_sub_self e
  ·
    have h1 : 1 - e = 0 := (hu.mul_right_eq_zero).mp h0
    refine Or.inr ?_
    apply (sub_eq_zero.mp h1).symm
  ·
    refine Or.inl ?_
    apply (hu.mul_left_eq_zero).mp h0

private lemma isLocalRing_of_surjective_of_isNilpotent
  [CommRing S] [CommRing T] [IsLocalRing T]
  {θ : S →+* T}
-- given
  (hθ : Function.Surjective θ)
  (hker : ∀ x, θ x = 0 → IsNilpotent x) :
-- imply
  IsLocalRing S := by
-- proof
  let _ : Nontrivial S := θ.domain_nontrivial
  have key : ∀ a : S, IsUnit (θ a) → IsUnit a := by
    intro a ha
    obtain ⟨c, hc⟩ := ha.exists_left_inv
    obtain ⟨b, rfl⟩ := hθ c
    have hn : IsNilpotent (b * a - 1) := hker _ (by rw [map_sub, map_mul, map_one, hc, sub_self])
    have hu : IsUnit (b * a - 1 + 1) := hn.isUnit_add_one
    rw [sub_add_cancel] at hu
    apply isUnit_of_mul_isUnit_right hu
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  obtain h | h := IsLocalRing.isUnit_or_isUnit_one_sub_self (θ a)
  ·
    apply Or.inl (key a h)
  ·
    refine Or.inr (key _ ?_)
    rwa [map_sub, map_one]

private lemma isLocalRing_of_isArtinianRing_of_forall_isIdempotentElem
  [CommRing R] [IsArtinianRing R] [Nontrivial R]
-- given
  (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
-- imply
  IsLocalRing R := by
-- proof
  obtain ⟨p, hpmax⟩ := Ideal.exists_maximal R
  let _ : p.IsPrime := hpmax.isPrime
  obtain ⟨r, hrp, hridem, hrq⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne p
  have hr1 : r = 1 := by
    obtain h | h := hR r hridem
    ·
      exfalso
      apply absurd (h ▸ p.zero_mem : r ∈ p) hrp
    ·
      apply h
  refine IsLocalRing.of_unique_max_ideal ⟨p, hpmax, fun q hq => ?_⟩
  by_contra hne
  apply hq.ne_top
  apply (Ideal.eq_top_iff_one q).mpr
  apply hr1 ▸ hrq q hq.isPrime hne

private lemma isLocalRing_tensorProduct_of_isAlgClosed
  {k : Type u} [Field k] [IsAlgClosed k]
  {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R] [Nontrivial R]
  {K : Type u} [Field K] [Algebra k K]
-- given
  (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
-- imply
  IsLocalRing (K ⊗[k] R) := by
-- proof
  let _ : IsArtinianRing R := IsArtinianRing.of_finite k R
  let _ : IsLocalRing R := isLocalRing_of_isArtinianRing_of_forall_isIdempotentElem hR
  set m : Ideal R := IsLocalRing.maximalIdeal R
  have hmnil : IsNilpotent m := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  let _ : m.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  let _ : Module.Finite k (R ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m).toLinearMap
      (Ideal.Quotient.mkₐ_surjective k m)
  have hbij : Function.Bijective (algebraMap k (R ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ m)
  let eκ : (R ⧸ m) ≃ₐ[k] k := (AlgEquiv.ofBijective (Algebra.ofId k (R ⧸ m)) hbij).symm
  let θ : K ⊗[k] R →ₐ[K] K ⊗[k] (R ⧸ m) :=
    Algebra.TensorProduct.map (AlgHom.id K K) (Ideal.Quotient.mkₐ k m)
  let eT : K ⊗[k] (R ⧸ m) ≃ₐ[K] K :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) eκ).trans
      (Algebra.TensorProduct.rid k K K)
  let _ : Nontrivial (K ⊗[k] (R ⧸ m)) := eT.symm.injective.nontrivial
  let _ : IsLocalRing (K ⊗[k] (R ⧸ m)) :=
    IsLocalRing.of_surjective' (eT.symm : K →+* K ⊗[k] (R ⧸ m)) eT.symm.surjective
  let g : R →ₗ[k] (R ⧸ m) := (Ideal.Quotient.mkₐ k m).toLinearMap
  let f : (m.restrictScalars k) →ₗ[k] R := (m.restrictScalars k).subtype
  have hg : Function.Surjective g := Ideal.Quotient.mkₐ_surjective k m
  have hfg : Function.Exact f g := by
    intro x
    constructor
    ·
      intro hx
      have hx' : x ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp hx
      refine ⟨⟨x, hx'⟩, rfl⟩
    ·
      rintro ⟨y, rfl⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr y.2
  have hexact := lTensor_exact K hfg hg
  have hθ_eq : ∀ x, θ x = LinearMap.lTensor K g x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a r =>
      simp [θ, g]
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy]
  apply isLocalRing_of_surjective_of_isNilpotent (θ := θ.toRingHom)
    (show Function.Surjective θ by
      intro y
      obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective K hg y
      refine ⟨x, ?_⟩
      rw [hθ_eq, hx])
    (show ∀ x, θ x = 0 → IsNilpotent x by
      intro x hx
      rw [hθ_eq] at hx
      obtain ⟨t, rfl⟩ := (hexact x).mp hx
      clear hx
      induction t using TensorProduct.inductionOn with
      | tmul a y =>
        have h1 : IsNilpotent ((1 : K) ⊗ₜ[k] (y : R)) := by
          obtain ⟨n, hn⟩ := hmnil
          refine ⟨n, ?_⟩
          have hy : (y : R) ^ n ∈ m ^ n := Ideal.pow_mem_pow y.2 n
          rw [hn] at hy
          have hy0 : (y : R) ^ n = 0 := by
            simpa using hy
          rw [Algebra.TensorProduct.tmul_pow, one_pow, hy0, TensorProduct.tmul_zero]
        have h2 : (a ⊗ₜ[k] (y : R) : K ⊗[k] R) =
          (a ⊗ₜ[k] (1 : R)) * ((1 : K) ⊗ₜ[k] (y : R)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
        simp only [LinearMap.lTensor_tmul, f, Submodule.coe_subtype]
        rw [h2]
        apply (Commute.all _ _).isNilpotent_mul_left h1
      | add x y hx hy =>
        rw [map_add]
        apply (Commute.all _ _).isNilpotent_add hx hy)


/--
[Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_TensorProduct_nontrivial_and_forall_isIdempotentElem_of_isAlgClosed.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k] [IsAlgClosed k]
  {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R] [Nontrivial R]
  {K : Type u} [Field K] [Algebra k K]
-- given
  (hR : ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1) :
-- imply
  Nontrivial (K ⊗[k] R) ∧ ∀ e : K ⊗[k] R, IsIdempotentElem e → e = 0 ∨ e = 1 := by
-- proof
  let _ : IsLocalRing (K ⊗[k] R) := isLocalRing_tensorProduct_of_isAlgClosed hR
  refine ⟨inferInstance, fun e he => ?_⟩
  apply eq_zero_or_eq_one_of_isIdempotentElem_of_isLocalRing he


-- created on 2026-10-13
