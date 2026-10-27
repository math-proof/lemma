import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma map_mem_maximalIdeal
  {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L]
  (πT : AlgHom 𝒪 L 𝒪)
  {z : L}
  -- given
  (hz : z ∈ maximalIdeal L) :
  -- imply
  πT z ∈ maximalIdeal 𝒪 := by
  -- proof
  by_contra hu
  have hunit : IsUnit (πT z) := of_not_not fun h => hu ((mem_maximalIdeal _).mpr h)
  have hk : πT (algebraMap 𝒪 L (πT z) - z) = 0 := by
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
  have hv : IsUnit (algebraMap 𝒪 L (πT z) - z) := by
    by_contra hnu
    have hm : algebraMap 𝒪 L (πT z) - z ∈ maximalIdeal L := (mem_maximalIdeal _).mpr hnu
    have : algebraMap 𝒪 L (πT z) ∈ maximalIdeal L := by
      have := Ideal.add_mem _ hm hz
      rwa [sub_add_cancel] at this
    apply (mem_maximalIdeal _).mp this (hunit.map _)
  have h1 : IsUnit (πT (algebraMap 𝒪 L (πT z) - z)) := hv.map πT
  rw [hk] at h1
  apply not_isUnit_zero h1

private lemma residue_point_eq
  {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] [IsLocalHom (algebraMap 𝒪 L)]
  (πT : AlgHom 𝒪 L 𝒪)
  (z : L)
  (x : ResidueField 𝒪)
  -- given
  (hz : residue L z = ResidueField.map (algebraMap 𝒪 L) x) :
  -- imply
  residue 𝒪 (πT z) = x := by
  -- proof
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : residue L z = residue L (algebraMap 𝒪 L a) := by
    rw [hz]
    rfl
  have h2 : z - algebraMap 𝒪 L a ∈ maximalIdeal L := by
    rw [← Ideal.Quotient.eq]
    apply h1
  have h3 : πT z - a ∈ maximalIdeal 𝒪 := by
    have := map_mem_maximalIdeal πT h2
    rwa [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at this
  show Ideal.Quotient.mk _ (πT z) = Ideal.Quotient.mk _ a
  apply (Ideal.Quotient.eq).mpr h3

/--
[IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_residue_algHom_apply_eq_of_residue_eq_map.lean)
-/
@[path]
private lemma main
  {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
  {L : Type} [CommRing L] [IsLocalRing L] [Algebra 𝒪 L] [IsLocalHom (algebraMap 𝒪 L)]
  (πT : AlgHom 𝒪 L 𝒪)
  (z : L)
  (x : ResidueField 𝒪)
  -- given
  (hz : residue L z = ResidueField.map (algebraMap 𝒪 L) x) :
  -- imply
  residue 𝒪 (πT z) = x :=
  residue_point_eq πT z x hz


-- created on 2026-10-20
