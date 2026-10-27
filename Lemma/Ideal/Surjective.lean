import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma map_maximalIdeal_le [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] (hres : Function.Surjective (⇑(Ideal.Quotient.mk (maximalIdeal A)) ∘ ⇑(algebraMap 𝒪 A))) : (maximalIdeal 𝒪).map (algebraMap 𝒪 A) ≤ maximalIdeal A := by
  rw [Ideal.map_le_iff_le_comap]
  let f : 𝒪 →+* A ⧸ maximalIdeal A := (Ideal.Quotient.mk (maximalIdeal A)).comp (algebraMap 𝒪 A)
  have hf : Function.Surjective f := hres
  let _ := Ideal.Quotient.field (maximalIdeal A)
  have hmax : (RingHom.ker f).IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have hker : RingHom.ker f = (maximalIdeal A).comap (algebraMap 𝒪 A) := by
    ext c
    rw [RingHom.mem_ker, Ideal.mem_comap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
  rw [← hker, eq_maximalIdeal hmax]
private lemma surjective_of_maximalIdeal_le_sup [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (maximalIdeal 𝒪) 𝒪] [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A] {J : Ideal A} (hJ : J ≤ maximalIdeal A) (hres : Function.Surjective (⇑(Ideal.Quotient.mk (maximalIdeal A)) ∘ ⇑(algebraMap 𝒪 A))) (hle : maximalIdeal A ≤ J ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 A)) : Function.Surjective (⇑(Ideal.Quotient.mk J) ∘ ⇑(algebraMap 𝒪 A)) := by
  have hJtop : J ≠ ⊤ := fun hJ' => (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (hJ' ▸ hJ))
  let _ : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  let _ : IsLocalRing (A ⧸ J) := .of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  let g : 𝒪 →+* A ⧸ J := (Ideal.Quotient.mk J).comp (algebraMap 𝒪 A)
  have hloc : (maximalIdeal 𝒪).map (algebraMap 𝒪 A) ≤ maximalIdeal A := map_maximalIdeal_le hres
  have hK : (maximalIdeal 𝒪).map g = ((maximalIdeal 𝒪).map (algebraMap 𝒪 A)).map (Ideal.Quotient.mk J) := (Ideal.map_map _ _).symm
  have hKtop : (maximalIdeal 𝒪).map g ≠ ⊤ := by
    intro htop
    have h1 : (1 : A ⧸ J) ∈ ((maximalIdeal 𝒪).map (algebraMap 𝒪 A)).map (Ideal.Quotient.mk J) := by
      rw [← hK, htop]
      trivial
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨m, hm, hm1⟩ := h1
    rw [← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq] at hm1
    have : (1 : A) ∈ maximalIdeal A := by
      have e : (1 : A) = m - (m - 1) := by ring
      rw [e]
      apply sub_mem (hloc hm) (hJ hm1)
    apply (maximalIdeal.isMaximal A).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  let _ : IsHausdorff ((maximalIdeal 𝒪).map g) (A ⧸ J) := IsHausdorff.of_isLocalRing _ _ hKtop
  refine surjective_of_mk_map_comp_surjective (I := maximalIdeal 𝒪) g ?_
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := hres (Ideal.Quotient.mk _ x)
  rw [Function.comp_apply] at hc
  rw [Ideal.Quotient.eq] at hc
  refine ⟨c, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, hK, RingHom.comp_apply, ← map_sub, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  obtain ⟨j, hj, t, ht, hjt⟩ := Submodule.mem_sup.mp (hle hc)
  refine ⟨t, ht, ?_⟩
  rw [Ideal.Quotient.eq, ← hjt]
  have : t - (j + t) = -j := by ring
  rw [this]
  apply J.neg_mem hj
private lemma helper_main [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (maximalIdeal 𝒪) 𝒪] [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A] (hres : Function.Surjective (⇑(residue A) ∘ ⇑(algebraMap 𝒪 A))) {J : Ideal A} (hle : maximalIdeal A ≤ J ⊔ maximalIdeal A ^ 2 ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 A)) : Function.Surjective (⇑(Ideal.Quotient.mk J) ∘ ⇑(algebraMap 𝒪 A)) := by
  if hJ : J = ⊤ then
    let _ : Subsingleton (A ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr hJ
    intro z
    exact ⟨0, Subsingleton.elim _ _⟩
  else
    apply surjective_of_maximalIdeal_le_sup (le_maximalIdeal hJ) hres (Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _) (maximalIdeal_le_jacobson _) _)
    refine hle.trans (le_of_eq ?_)
    rw [Ideal.smul_eq_mul, ← pow_two, sup_right_comm]
/--
[IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_mk_comp_algebraMap_surjective_of_maximalIdeal_le.lean)
-/
@[path]
private lemma main
  {𝒪 : Type u} {A : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [IsPrecomplete (IsLocalRing.maximalIdeal 𝒪) 𝒪] [CommRing A] [Algebra 𝒪 A] [IsLocalRing A] [IsNoetherianRing A]
  (hres : Function.Surjective (⇑(IsLocalRing.residue A) ∘ ⇑(algebraMap 𝒪 A)))
  {J : Ideal A}
  (hle : IsLocalRing.maximalIdeal A ≤ J ⊔ IsLocalRing.maximalIdeal A ^ 2 ⊔ (IsLocalRing.maximalIdeal 𝒪).map (algebraMap 𝒪 A)) :
  -- imply
  Function.Surjective (⇑(Ideal.Quotient.mk J) ∘ ⇑(algebraMap 𝒪 A)) :=
  helper_main hres hle


-- created on 2026-10-20
