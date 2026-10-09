import sympy.Basic
import Mathlib
import Lemma.AdicCompletion.exists.RingEquiv.of.IsLocalization.AtPrime.of.IsMaximal

/-! transportHom via FLT RingFunctoriality mapₐ (ported in IsMaximal). -/
namespace AdicCompletion

theorem transportHom_map_le {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) :
    I.map f.toIntAlgHom ≤ J := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have h : I ≤ J.comap f := by simpa [pow_one] using hf 1
  exact h hx

noncomputable def transportHom {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) : AdicCompletion I R →+* AdicCompletion J S :=
  (mapₐ I J f.toIntAlgHom (transportHom_map_le I J f hf)).toRingHom

theorem evalₐ_transportHom {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f)
    (n : ℕ) (x : AdicCompletion I R) :
    evalₐ J n (transportHom I J f hf x) =
      Ideal.quotientMap (J ^ n) f (hf n) (evalₐ I n x) := by
  rw [transportHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evalₐ_mapₐ]
  -- levelMapₐ = quotientMapₐ; need to match Ideal.quotientMap
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  rw [← hr, levelMapₐ_mk]
  rfl

end AdicCompletion

-- export at root for existing call sites
noncomputable abbrev transportHom {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S)
    (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f) := AdicCompletion.transportHom I J f hf

noncomputable abbrev evalₐ_transportHom {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : ∀ n : ℕ, I ^ n ≤ (J ^ n).comap f)
    (n : ℕ) (x : AdicCompletion I R) := AdicCompletion.evalₐ_transportHom I J f hf n x

/--
[AdicCompletion_exists_ringEquiv_map_of_ringEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_exists_ringEquiv_map_of_ringEquiv.lean)
-/
@[path]
private lemma main
  {R : Type u} {S : Type v} [CommRing R] [CommRing S]
-- given
  (I : Ideal R) (e : R ≃+* S) :
-- imply
  ∃ ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S,
      ∀ r : R, ê (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion (I.map e) S) (e r) := by
-- proof
  classical
  have hJn : ∀ n : ℕ, (I.map e) ^ n = (I ^ n).map (e : R →+* S) := fun n => (Ideal.map_pow (e : R →+* S) I n).symm
  have hf : ∀ n : ℕ, I ^ n ≤ ((I.map e) ^ n).comap (e : R →+* S) := by
    intro n x hx
    rw [Ideal.mem_comap, hJn]
    exact Ideal.mem_map_of_mem _ hx
  have hg : ∀ n : ℕ, (I.map e) ^ n ≤ (I ^ n).comap (e.symm : S →+* R) := by
    intro n y hy
    rw [hJn, Ideal.map_comap_of_equiv] at hy
    exact hy
  let φ := transportHom I (I.map e) (e : R →+* S) hf
  let ψ := transportHom (I.map e) I (e.symm : S →+* R) hg
  have hφψ : ∀ y, φ (ψ y) = y := by
    intro y
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_transportHom, evalₐ_transportHom]
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (I.map e) n y)
    rw [← hs, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    simp
  have hψφ : ∀ x, ψ (φ x) = x := by
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [evalₐ_transportHom, evalₐ_transportHom]
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    rw [← hr, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    simp
  let ê : AdicCompletion I R ≃+* AdicCompletion (I.map e) S :=
    { toFun := φ, invFun := ψ, left_inv := hψφ, right_inv := hφψ,
      map_mul' := fun x y => φ.map_mul x y, map_add' := fun x y => φ.map_add x y }
  refine ⟨ê, fun r => ?_⟩
  show φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion (I.map e) S) (e r)
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_transportHom, AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    Algebra.algebraMap_self, RingHom.id_apply, RingHom.id_apply, AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  rfl

-- created on 2026-10-09
