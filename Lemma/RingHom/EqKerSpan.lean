import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma counit_of
  {𝒪 : Type u} [CommRing 𝒪]
  {G : Type v} [Group G]
  (g : G) :
  -- imply
  Coalgebra.counit (R := 𝒪) (MonoidAlgebra.of 𝒪 G g) = 1 := by
  -- proof
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.counit_single, CommSemiring.counit_apply]

private lemma of_sub_one_mem_span
  {𝒪 : Type u} [CommRing 𝒪]
  {G : Type v} [Group G]
  (S : Set G)
  (g : G)
  -- given
  (hS : Subgroup.closure S = ⊤) :
  -- imply
  MonoidAlgebra.of 𝒪 G g - 1 ∈ Ideal.span ((fun g => MonoidAlgebra.of 𝒪 G g - 1) '' S) := by
  -- proof
  set J := Ideal.span ((fun g => MonoidAlgebra.of 𝒪 G g - 1) '' S)
  have hg : g ∈ Subgroup.closure S := by
    rw [hS]
    apply Subgroup.mem_top g
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    apply Ideal.subset_span
    refine ⟨s, hs, rfl⟩
  | one =>
    rw [map_one, sub_self]
    apply J.zero_mem
  | mul a b _ _ ha hb =>
    have : MonoidAlgebra.of 𝒪 G (a * b) - 1 =
      MonoidAlgebra.of 𝒪 G a * (MonoidAlgebra.of 𝒪 G b - 1) + (MonoidAlgebra.of 𝒪 G a - 1) := by
      rw [map_mul, mul_sub, mul_one, sub_add_sub_cancel]
    rw [this]
    apply J.add_mem (J.mul_mem_left _ hb) ha
  | inv a _ ha =>
    have : MonoidAlgebra.of 𝒪 G a⁻¹ - 1 = -(MonoidAlgebra.of 𝒪 G a⁻¹) * (MonoidAlgebra.of 𝒪 G a - 1) := by
      rw [neg_mul, mul_sub, mul_one, ← map_mul, inv_mul_cancel, map_one, neg_sub]
    rw [this]
    apply J.mul_mem_left _ ha

/--
[MonoidAlgebra_ker_counitAlgHom_eq_span_of_closure_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidAlgebra_ker_counitAlgHom_eq_span_of_closure_eq_top.lean)
-/
@[path]
private lemma main
  {𝒪 : Type u} [CommRing 𝒪]
  {G : Type v} [Group G]
  (S : Set G)
  -- given
  (hS : Subgroup.closure S = ⊤) :
  -- imply
  RingHom.ker (Bialgebra.counitAlgHom 𝒪 (MonoidAlgebra 𝒪 G)) =
    Ideal.span ((fun g => MonoidAlgebra.of 𝒪 G g - 1) '' S) := by
  -- proof
  apply le_antisymm
  ·
    intro x hx
    rw [RingHom.mem_ker, Bialgebra.counitAlgHom_apply] at hx
    have hdecomp : x = x.coeff.sum (fun g a => a • (MonoidAlgebra.of 𝒪 G g - 1)) +
        algebraMap 𝒪 (MonoidAlgebra 𝒪 G) (Coalgebra.counit (R := 𝒪) x) := by
      have hc : Coalgebra.counit (R := 𝒪) x = x.coeff.sum (fun _ a => a) := by
        conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x]
        rw [Finsupp.sum, map_sum, Finsupp.sum]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [MonoidAlgebra.counit_single, CommSemiring.counit_apply]
      rw [hc, Finsupp.sum, Finsupp.sum, map_sum, ← Finset.sum_add_distrib]
      conv_lhs => rw [← MonoidAlgebra.sum_coeff_single x, Finsupp.sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [smul_sub, Algebra.algebraMap_eq_smul_one, sub_add_cancel, MonoidAlgebra.of_apply,
        MonoidAlgebra.smul_single', mul_one]
    rw [hdecomp, hx, map_zero, add_zero, Finsupp.sum]
    apply Submodule.sum_mem _ fun g _ => Submodule.smul_of_tower_mem _ _ (of_sub_one_mem_span S g hS)
  ·
    rw [Ideal.span_le]
    rintro _ ⟨s, -, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, Bialgebra.counitAlgHom_apply, counit_of, map_one, sub_self]


-- created on 2026-10-20
