import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Polynomial.mem_range_of_unique_common_root {F L : Type u} [Field F] [Field L] [Algebra F L] (A B : Polynomial F) (hA : A ≠ 0) (hAs : (A.map (algebraMap F L)).Splits) (hAnd : (A.map (algebraMap F L)).roots.Nodup) (x : L) (hxA : Polynomial.aeval x A = 0) (hxB : Polynomial.aeval x B = 0) (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) : x ∈ (algebraMap F L).range := by
  classical
  set i := algebraMap F L
  set g := EuclideanDomain.gcd A B with hg
  have hg0 : g ≠ 0 := fun h => hA (EuclideanDomain.gcd_eq_zero_iff.mp h).1
  have hgA : g ∣ A := EuclideanDomain.gcd_dvd_left _ _
  have hgB : g ∣ B := EuclideanDomain.gcd_dvd_right _ _
  have hAm0 : A.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hA
  have hgm0 : g.map i ≠ 0 := (Polynomial.map_ne_zero_iff i.injective).mpr hg0
  have hxg : Polynomial.aeval x g = 0 := by rw [hg, EuclideanDomain.gcd_eq_gcd_ab A B, map_add, map_mul, map_mul, hxA, hxB, zero_mul, zero_mul, add_zero]
  have hroot_eq : ∀ y ∈ (g.map i).roots, y = x := by
    intro y hy
    rw [Polynomial.mem_roots hgm0, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap] at hy
    refine huniq y ?_ ?_
    ·
      obtain ⟨c, hc⟩ := hgA
      rw [hc, map_mul, hy, zero_mul]
    ·
      obtain ⟨c, hc⟩ := hgB
      rw [hc, map_mul, hy, zero_mul]
  have hxmem : x ∈ (g.map i).roots := by
    rw [Polynomial.mem_roots hgm0, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
    apply hxg
  have hle : (g.map i).roots ≤ (A.map i).roots := Polynomial.roots.le_of_dvd hAm0 (Polynomial.map_dvd i hgA)
  have hnd : (g.map i).roots.Nodup := Multiset.nodup_of_le hle hAnd
  have hcount : (g.map i).roots.count x = Multiset.card (g.map i).roots := Multiset.count_eq_card.mpr fun y hy => (hroot_eq y hy).symm
  have hcard : Multiset.card (g.map i).roots = 1 := by
    have h1 : (g.map i).roots.count x ≤ 1 := Multiset.nodup_iff_count_le_one.mp hnd x
    have h2 : 0 < (g.map i).roots.count x := Multiset.count_pos.mpr hxmem
    omega
  have hgs : (g.map i).Splits := Polynomial.Splits.of_dvd hAs hAm0 (Polynomial.map_dvd i hgA)
  have hdeg : g.natDegree = 1 := by rw [← Polynomial.natDegree_map i, hgs.natDegree_eq_card_roots, hcard]
  refine (Polynomial.Splits.of_natDegree_eq_one hdeg).mem_range_of_isRoot hg0 ((Polynomial.mem_roots hgm0).mp hxmem)
/--
[Polynomial_mem_range_of_unique_common_root](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_mem_range_of_unique_common_root.lean)
-/
@[path]
private lemma main
  {F L : Type u} [Field F] [Field L] [Algebra F L]
  (A B : Polynomial F)
  (x : L)
  -- given
  (hA : A ≠ 0)
  (hAs : (A.map (algebraMap F L)).Splits)
  (hAnd : (A.map (algebraMap F L)).roots.Nodup)
  (hxA : Polynomial.aeval x A = 0)
  (hxB : Polynomial.aeval x B = 0)
  (huniq : ∀ y : L, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x) :
  -- imply
  x ∈ (algebraMap F L).range :=
  Polynomial.mem_range_of_unique_common_root A B hA hAs hAnd x hxA hxB huniq


-- created on 2026-10-20
