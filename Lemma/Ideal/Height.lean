import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma eq_of_le_of_under_eq
  {P B : Type u} [CommRing P] [CommRing B] [Algebra P B] [Algebra.IsIntegral P B]
  {Q q : Ideal B} [Q.IsPrime] [q.IsPrime]
  (hle : Q ≤ q) (hu : q.under P ≤ Q.under P) :
  -- imply
  Q = q := by
  -- proof
  by_contra hne
  have hlt : Q < q := lt_of_le_of_ne hle hne
  obtain ⟨x, hxq, hxQ⟩ := Set.exists_of_ssubset hlt
  have hcomap := Ideal.under_lt_under_of_integral_mem_sdiff hle ⟨hxq, hxQ⟩ (Algebra.IsIntegral.isIntegral (R := P) x)
  refine absurd (lt_of_lt_of_le hcomap hu) (lt_irrefl _)

private lemma height_eq_height_under
  (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B] [Algebra.IsIntegral P B]
  (q : Ideal B) [q.IsPrime] :
  -- imply
  q.height = (q.under P).height := by
  -- proof
  set p := q.under P with hp
  set I := Ideal.map (algebraMap P B) p with hI
  have hIq : I ≤ q := Ideal.map_comap_le
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ q := by
    rw [Ideal.mk_ker]
    apply hIq
  let hQbar : (Ideal.map (Ideal.Quotient.mk I) q).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have key := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p q
  suffices h0 : (Ideal.map (Ideal.Quotient.mk I) q).height = 0 by
    rw [key, ← hI, h0, add_zero]
  refine nonpos_iff_eq_zero.mp ?_
  rw [← ENat.natCast_zero, Ideal.height_le_iff]
  intro Q' hQ' hQ'lt
  exfalso
  set Q := Ideal.comap (Ideal.Quotient.mk I) Q' with hQ
  have hIQ : I ≤ Q := (Ideal.mk_ker (I := I)).symm.trans_le (Ideal.ker_le_comap _)
  have hQq : Q ≤ q := by
    refine (Ideal.comap_mono hQ'lt.le).trans ?_
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective]
    refine sup_le le_rfl ?_
    rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    apply hIq
  have hunder : q.under P ≤ Q.under P := by
    change p ≤ Ideal.comap (algebraMap P B) Q
    apply Ideal.le_comap_of_map_le hIQ
  have hQeq : Q = q := eq_of_le_of_under_eq hQq hunder
  have hQ'eq : Ideal.map (Ideal.Quotient.mk I) Q = Q' := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective _
  rw [hQeq] at hQ'eq
  apply absurd (hQ'eq ▸ hQ'lt) (lt_irrefl _)

/--
[Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral.lean)
-/
@[path]
private lemma main
  (P B : Type u) [CommRing P] [IsDomain P] [IsNoetherianRing P] [IsIntegrallyClosed P]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [Algebra P B] [FaithfulSMul P B] [Algebra.IsIntegral P B]
  (q : Ideal B) [q.IsPrime] :
  -- imply
  q.height = (q.under P).height :=
  height_eq_height_under P B q


-- created on 2026-10-20
