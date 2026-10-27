import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma counit_of {𝒪 : Type u} [CommRing 𝒪] {G : Type v} [CommGroup G] (g : G) : Coalgebra.counit (R := 𝒪) (MonoidAlgebra.of 𝒪 G g) = 1 := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]
private lemma sub_algebraMap_counit_mem {𝒪 : Type u} [CommRing 𝒪] {G : Type v} [CommGroup G] (x : MonoidAlgebra 𝒪 G) : x - algebraMap 𝒪 (MonoidAlgebra 𝒪 G) (Coalgebra.counit (R := 𝒪) x) ∈ Ideal.span (Set.range fun g : G => MonoidAlgebra.of 𝒪 G g - 1) := by
  set J := Ideal.span (Set.range fun g : G => MonoidAlgebra.of 𝒪 G g - 1)
  have hc : Coalgebra.counit (R := 𝒪) x = x.coeff.sum (fun _ a => a) := by
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
    rw [Finsupp.sum, map_sum, Finsupp.sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
  have hdecomp : x - algebraMap 𝒪 (MonoidAlgebra 𝒪 G) (Coalgebra.counit (R := 𝒪) x) = x.coeff.sum (fun g a => a • (MonoidAlgebra.of 𝒪 G g - 1)) := by
    rw [sub_eq_iff_eq_add, hc, Finsupp.sum, Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
    conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x, Finsupp.sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [smul_sub, Algebra.algebraMap_eq_smul_one, sub_add_cancel, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rw [hdecomp, Finsupp.sum]
  apply Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ (Ideal.subset_span (by refine ⟨g, rfl⟩))
private lemma of_sub_one_pow_mem {𝒪 : Type u} [CommRing 𝒪] {G : Type v} [CommGroup G] {p : ℕ} [Fact p.Prime] (g : G) (k : ℕ) (hg : g ^ p ^ k = 1) : (MonoidAlgebra.of 𝒪 G g - 1) ^ p ^ k ∈ Ideal.span {(p : MonoidAlgebra 𝒪 G)} := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq (Fact.out : p.Prime) (MonoidAlgebra.of 𝒪 G g) (-1) k
  rw [sub_eq_add_neg, hr, ← map_pow, hg, map_one]
  obtain hev | hodd := Nat.even_or_odd (p ^ k)
  ·
    have hp2 : p = 2 := ((Fact.out : p.Prime).even_iff).mp (Nat.even_pow.mp hev).1
    have h11 : (1 : MonoidAlgebra 𝒪 G) + 1 = (p : MonoidAlgebra 𝒪 G) := by rw [hp2, Nat.cast_two, one_add_one_eq_two]
    rw [hev.neg_one_pow, h11, mul_assoc, mul_assoc]
    apply Ideal.add_mem _ (Ideal.mem_span_singleton_self _) (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  ·
    rw [hodd.neg_one_pow, add_neg_cancel, zero_add, mul_assoc, mul_assoc]
    apply Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
private lemma isUnit_one_add_of_mem_map {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] {G : Type v} [CommGroup G] [Finite G] {m : MonoidAlgebra 𝒪 G} (hm : m ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 (MonoidAlgebra 𝒪 G))) : IsUnit (1 + m) := by
  let μ : MonoidAlgebra 𝒪 G →ₗ[𝒪] MonoidAlgebra 𝒪 G := LinearMap.mulLeft 𝒪 (1 + m)
  have hle : (⊤ : Submodule 𝒪 (MonoidAlgebra 𝒪 G)) ≤ LinearMap.range μ ⊔ (maximalIdeal 𝒪) • ⊤ := by
    intro x _
    have hx : x = (1 + m) * x - m * x := by ring
    rw [hx]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left ⟨x, rfl⟩) (Submodule.mem_sup_right ?_)
    rw [Ideal.smul_top_eq_map]
    apply Ideal.mul_mem_right _ _ hm
  have htop : (⊤ : Submodule 𝒪 (MonoidAlgebra 𝒪 G)) ≤ LinearMap.range μ := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (maximalIdeal_le_jacobson _) hle
  obtain ⟨y, hy⟩ : (1 : MonoidAlgebra 𝒪 G) ∈ LinearMap.range μ := htop Submodule.mem_top
  apply IsUnit.of_mul_eq_one y hy
private lemma exists_pow_augIdeal_le {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] {p : ℕ} [Fact p.Prime] {G : Type v} [CommGroup G] [Finite G] (hp : (p : 𝒪) ∈ maximalIdeal 𝒪) (hG : IsPGroup p G) : ∃ N : ℕ, Ideal.span (Set.range fun g : G => MonoidAlgebra.of 𝒪 G g - 1) ^ N ≤ (maximalIdeal 𝒪).map (algebraMap 𝒪 (MonoidAlgebra 𝒪 G)) := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.span_le]
  intro _ hg
  obtain ⟨g, rfl⟩ := hg
  obtain ⟨k, hk⟩ := hG g
  refine ⟨p ^ k, ?_⟩
  apply (Ideal.span_singleton_le_iff_mem _).mpr _ (of_sub_one_pow_mem g k hk)
  rw [← map_natCast (algebraMap 𝒪 (MonoidAlgebra 𝒪 G))]
  apply Ideal.mem_map_of_mem _ hp
private lemma isUnit_one_add_of_mem_augIdeal {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] {p : ℕ} [Fact p.Prime] {G : Type v} [CommGroup G] [Finite G] (hp : (p : 𝒪) ∈ maximalIdeal 𝒪) (hG : IsPGroup p G) {i : MonoidAlgebra 𝒪 G} (hi : i ∈ Ideal.span (Set.range fun g : G => MonoidAlgebra.of 𝒪 G g - 1)) : IsUnit (1 + i) := by
  obtain ⟨N, hN⟩ := exists_pow_augIdeal_le (𝒪 := 𝒪) (G := G) hp hG
  have hiN : (-i) ^ N ∈ (maximalIdeal 𝒪).map (algebraMap 𝒪 (MonoidAlgebra 𝒪 G)) := by
    rw [neg_pow]
    apply Ideal.mul_mem_left _ _ (hN (Ideal.pow_mem_pow hi N))
  have hgeom : (1 + i) * ∑ j ∈ Finset.range N, (-i) ^ j = 1 + -(-i) ^ N := by
    have := mul_neg_geom_sum (-i) N
    rw [sub_neg_eq_add] at this
    rw [this, sub_eq_add_neg]
  apply isUnit_of_mul_isUnit_left
  rw [hgeom]
  apply isUnit_one_add_of_mem_map ((Ideal.neg_mem_iff _).mpr hiN)
private lemma isUnit_of_counit_not_mem {𝒪 : Type u} [CommRing 𝒪] [IsLocalRing 𝒪] {p : ℕ} [Fact p.Prime] {G : Type v} [CommGroup G] [Finite G] (hp : (p : 𝒪) ∈ maximalIdeal 𝒪) (hG : IsPGroup p G) {x : MonoidAlgebra 𝒪 G} (hx : Coalgebra.counit (R := 𝒪) x ∉ maximalIdeal 𝒪) : IsUnit x := by
  set c := Coalgebra.counit (R := 𝒪) x
  have hc : IsUnit c := by
    by_contra h
    apply hx ((mem_maximalIdeal _).mpr h)
  obtain ⟨u, hu⟩ := hc
  have hdecomp : x = algebraMap 𝒪 (MonoidAlgebra 𝒪 G) c * (1 + algebraMap 𝒪 (MonoidAlgebra 𝒪 G) (↑u⁻¹ : 𝒪) * (x - algebraMap 𝒪 (MonoidAlgebra 𝒪 G) c)) := by
    rw [mul_add, mul_one, ← mul_assoc, ← map_mul, ← hu, Units.mul_inv, map_one, one_mul, add_sub_cancel]
  rw [hdecomp]
  refine ((hu ▸ Units.isUnit u).map (algebraMap 𝒪 (MonoidAlgebra 𝒪 G))).mul ?_
  apply isUnit_one_add_of_mem_augIdeal hp hG (Ideal.mul_mem_left _ _ (sub_algebraMap_counit_mem x))
/--
[MonoidAlgebra_isLocalRing_of_isPGroup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidAlgebra_isLocalRing_of_isPGroup.lean)
-/
@[path]
private lemma main
  {𝒪 : Type u} {p : ℕ} {G : Type v} [CommRing 𝒪] [IsLocalRing 𝒪] [Fact p.Prime] [CommGroup G] [Finite G]
  -- given
  (hp : (p : 𝒪) ∈ maximalIdeal 𝒪)
  (hG : IsPGroup p G) :
  -- imply
  IsLocalRing (MonoidAlgebra 𝒪 G) := by
  -- proof
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  if ha : Coalgebra.counit (R := 𝒪) a ∈ maximalIdeal 𝒪 then
    apply Or.inr
    refine isUnit_of_counit_not_mem hp hG ?_
    intro h1
    have : Coalgebra.counit (R := 𝒪) (1 : MonoidAlgebra 𝒪 G) = 1 := by
      rw [MonoidAlgebra.one_def, MonoidAlgebra.counit_single, CommSemiring.counit_apply]
    rw [map_sub, this] at h1
    apply (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using (maximalIdeal 𝒪).add_mem h1 ha))
  else
    apply Or.inl (isUnit_of_counit_not_mem hp hG ha)


-- created on 2026-10-20
