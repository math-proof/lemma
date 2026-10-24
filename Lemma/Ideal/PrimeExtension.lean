import Mathlib
import sympy.Basic


namespace Ideal

variable {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
/--
[quotientMap_bijectiveOfClearDenom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
Under the hypotheses of `Ideal.isPrime_map_of_coprime_clearDenom`, the canonical
map `O ⧸ p → B ⧸ p.map (algebraMap O B)` is bijective. This bundles the injective
and surjective parts so the primality and maximality corollaries share one proof. -/
private lemma quotientMap_bijectiveOfClearDenom (p c : Ideal O) (hp : p.IsPrime)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B,
    algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) : Function.Bijective
    (quotientMap (p.map (algebraMap O B)) (algebraMap O B) le_comap_map) := by
  obtain ⟨y, hyc, z, hzp, hyz⟩ :=
    Submodule.mem_sup.mp ((eq_top_iff_one _).mp hsup)
  have hyP : y ∉ p := by
    intro hymem
    apply hp.ne_top
    rw [eq_top_iff_one, ← hyz]
    exact p.add_mem hymem hzp
  -- Clearing one multiple of `y` at a time: every `w ∈ p.map f` satisfies
  -- `f y * (b * w) = f t` for some `t ∈ p`, uniformly in `b`.
  have key : ∀ w ∈ p.map (algebraMap O B), ∀ b : B,
    ∃ t ∈ p, algebraMap O B y * (b * w) = algebraMap O B t := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro b
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨s, hs⟩ := hclear y hyc b
      exact ⟨s * q, p.mul_mem_left s (SetLike.mem_coe.mp hq), by
        rw [← mul_assoc, ← hs, map_mul]⟩
    | zero =>
      intro b
      exact ⟨0, p.zero_mem, by simp⟩
    | add x₁ x₂ _ _ ih₁ ih₂ =>
      intro b
      obtain ⟨t₁, ht₁, e₁⟩ := ih₁ b
      obtain ⟨t₂, ht₂, e₂⟩ := ih₂ b
      have e : b * (x₁ + x₂) = b * x₁ + b * x₂ := mul_add _ _ _
      exact ⟨t₁ + t₂, p.add_mem ht₁ ht₂, by rw [e, mul_add, e₁, e₂, map_add]⟩
    | smul a x _ ih =>
      intro b
      obtain ⟨t, ht, e⟩ := ih (b * a)
      refine ⟨t, ht, ?_⟩
      rwa [smul_eq_mul, ← mul_assoc b a x]
  have hcomap : (p.map (algebraMap O B)).comap (algebraMap O B) ≤ p := by
    intro x hx
    have hmem : algebraMap O B x ∈ p.map (algebraMap O B) := hx
    obtain ⟨t, htP, e⟩ := key _ hmem 1
    rw [one_mul] at e
    have e₂ : algebraMap O B (y * x) = algebraMap O B t := by
      rwa [map_mul]
    have hyx : y * x ∈ p := by
      rwa [hinj e₂]
    exact (hp.mem_or_mem hyx).resolve_left hyP
  have hinjQ : Function.Injective
    (quotientMap (p.map (algebraMap O B)) (algebraMap O B) le_comap_map) :=
    quotientMap_injective' (H := le_comap_map) hcomap
  have hsurjQ : Function.Surjective
    (quotientMap (p.map (algebraMap O B)) (algebraMap O B) le_comap_map) := by
    intro q
    obtain ⟨b, rfl⟩ := Quotient.mk_surjective q
    obtain ⟨t, ht⟩ := hclear y hyc b
    refine ⟨Quotient.mk p t, ?_⟩
    rw [quotientMap_mk]
    have hfz : algebraMap O B y + algebraMap O B z = 1 := by
      have h := congrArg (algebraMap O B) hyz
      simpa using h
    have hz : (1 : B) - algebraMap O B y = algebraMap O B z := by
      rw [← hfz, add_sub_cancel_left]
    have hdiff : b - algebraMap O B t = algebraMap O B z * b := by
      rw [ht, ← hz]
      ring
    have hmem : b - algebraMap O B t ∈ p.map (algebraMap O B) := by
      rw [hdiff]
      exact (p.map (algebraMap O B)).mul_mem_right b (mem_map_of_mem _ hzp)
    have hmem₂ : algebraMap O B t - b ∈ p.map (algebraMap O B) := by
      have hneg := neg_mem hmem
      rwa [neg_sub] at hneg
    have h0 : Quotient.mk (p.map (algebraMap O B)) (algebraMap O B t) -
      Quotient.mk (p.map (algebraMap O B)) b = 0 := by
      rw [← map_sub]
      exact Quotient.eq_zero_iff_mem.mpr hmem₂
    exact sub_eq_zero.mp h0
  exact ⟨hinjQ, hsurjQ⟩

end Ideal

namespace Ideal

/--
[isPrime_map_of_coprime_clearDenom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
lemma isPrime_map_of_coprime_clearDenom
  [CommRing O] [CommRing B] [Algebra O B]
  {p c : Ideal O}
-- given
  (hp : p.IsPrime)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B, algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) :
-- imply
  (p.map (algebraMap O B)).IsPrime := by
-- proof
  let e : O ⧸ p ≃+* B ⧸ p.map (algebraMap O B) :=
    RingEquiv.ofBijective _ (quotientMap_bijectiveOfClearDenom p c hp hinj hclear hsup)
  have : IsDomain (O ⧸ p) := (Quotient.isDomain_iff_prime _).mpr hp
  have : Nontrivial (B ⧸ p.map (algebraMap O B)) := e.symm.surjective.nontrivial
  have : NoZeroDivisors (B ⧸ p.map (algebraMap O B)) :=
    e.symm.injective.noZeroDivisors _ (map_zero _) (fun x y => map_mul _ _ _)
  have : IsDomain (B ⧸ p.map (algebraMap O B)) := NoZeroDivisors.to_isDomain _
  exact (Quotient.isDomain_iff_prime _).mp inferInstance

end Ideal

namespace Ideal

/--
[isMaximal_map_of_coprime_clearDenom](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
lemma isMaximal_map_of_coprime_clearDenom
  [CommRing O] [CommRing B] [Algebra O B]
  {p c : Ideal O}
-- given
  (hp : p.IsMaximal)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B, algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) :
-- imply
  (p.map (algebraMap O B)).IsMaximal := by
-- proof
  let e : O ⧸ p ≃+* B ⧸ p.map (algebraMap O B) := RingEquiv.ofBijective _
    (quotientMap_bijectiveOfClearDenom p c hp.isPrime hinj hclear hsup)
  have := hp
  let fld : Field (O ⧸ p) := Quotient.field p
  have hF : IsField (O ⧸ p) := Field.toIsField _
  have hFB : IsField (B ⧸ p.map (algebraMap O B)) := e.symm.toMulEquiv.isField hF
  exact Quotient.maximal_of_isField _ hFB

end Ideal

namespace Ideal

/--
[isMaximal_map_of_dimensionLEOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Ideal/PrimeExtension.lean)
-/
@[path]
lemma isMaximal_map_of_dimensionLEOne
  [CommRing O] [CommRing B] [Algebra O B] [Ring.DimensionLEOne O]
  {p c : Ideal O}
-- given
  (hp : p.IsPrime)
  (hne : p ≠ ⊥)
  (hinj : Function.Injective (algebraMap O B))
  (hclear : ∀ x ∈ c, ∀ b : B, algebraMap O B x * b ∈ Set.range (algebraMap O B))
  (hsup : c ⊔ p = ⊤) :
-- imply
  (p.map (algebraMap O B)).IsMaximal :=
-- proof
  isMaximal_map_of_coprime_clearDenom p c (hp.isMaximal hne) hinj hclear hsup

end Ideal


-- created on 2026-10-20
-- updated on 2026-10-23
