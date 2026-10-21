import Mathlib
import sympy.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma nontrivial_quotient_of_ne_top
  {A : Type} [CommRing A]
  {I : Ideal A}
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  Nontrivial (A ⧸ I) :=
  Ideal.Quotient.nontrivial_iff.mpr hI

private lemma isLocalRing_quotient_of_ne_top
  {A : Type} [CommRing A] [IsLocalRing A]
  {I : Ideal A}
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  IsLocalRing (A ⧸ I) :=
  let _ := nontrivial_quotient_of_ne_top hI
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

private lemma isLocalHom_mk_of_ne_top
  {A : Type} [CommRing A] [IsLocalRing A]
  {I : Ideal A}
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  IsLocalHom (Ideal.Quotient.mk I) :=
  let _ := nontrivial_quotient_of_ne_top hI
  IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective

private lemma map_maximalIdeal_mk_of_ne_top
  {A : Type} [CommRing A] [IsLocalRing A]
  {I : Ideal A} [IsLocalRing (A ⧸ I)]
  -- given
  (hI : I ≠ ⊤) :
  -- imply
  (maximalIdeal A).map (Ideal.Quotient.mk I) = maximalIdeal (A ⧸ I) := by
  -- proof
  let _ := isLocalHom_mk_of_ne_top hI
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr (le_maximalIdeal hI), mem_maximalIdeal,
    mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_map_iff]

/--
[IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow.lean)
-/
@[path]
private lemma main
  {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  (m : ℕ) :
  -- imply
  IsArtinianRing (A ⧸ maximalIdeal A ^ (m + 1)) := by
  -- proof
  have hne : maximalIdeal A ^ (m + 1) ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal A).ne_top (top_le_iff.mp (h ▸ Ideal.pow_le_self m.succ_ne_zero))
  let _ := isLocalRing_quotient_of_ne_top hne
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal, ← map_maximalIdeal_mk_of_ne_top hne]
  refine ⟨m + 1, by rw [← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]⟩


-- created on 2026-10-20
