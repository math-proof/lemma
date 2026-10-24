import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[IsIntegrallyClosed_of_directed_iUnion_subring](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsIntegrallyClosed_of_directed_iUnion_subring.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] [IsDomain B] {ι : Type v} [Nonempty ι] (S : ι → Subring B)
    (hdir : Directed (· ≤ ·) S) (hcov : ∀ x : B, ∃ i, x ∈ S i)
    (hS : ∀ i, IsIntegrallyClosed (S i)) :
    -- imply
    IsIntegrallyClosed B := by
    -- proof
  classical
  let K := FractionRing B
  rw [isIntegrallyClosed_iff K]
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  choose f hf using hcov
  obtain ⟨i, hi⟩ := hdir.finset_le
    (insert (f a) (insert (f b) ((Finset.range (p.natDegree + 1)).image fun n => f (p.coeff n))))
  have ha : a ∈ S i := hi _ (Finset.mem_insert_self _ _) (hf a)
  have hbS : b ∈ S i := hi _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) (hf b)
  have hcoeff : ∀ n, p.coeff n ∈ S i := by
    intro n
    if hn : n < p.natDegree + 1 then
      apply hi _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩))) (hf _)
    else
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      apply zero_mem _
  set T : Subring B := S i with hT
  let _ : IsIntegrallyClosed T := hS i
  have hinjTB : Function.Injective (algebraMap T B) := Subtype.val_injective
  have hinjTK : Function.Injective (algebraMap T K) := by
    rw [IsScalarTower.algebraMap_eq T B K]
    apply (IsFractionRing.injective B K).comp hinjTB
  let φ : FractionRing T →ₐ[T] K := { IsFractionRing.lift hinjTK with commutes' := fun t => by simp [IsFractionRing.lift_algebraMap] }
  have hφ : ∀ y, φ y = IsFractionRing.lift hinjTK y := fun _ => rfl
  have hφinj : Function.Injective φ := (IsFractionRing.lift hinjTK : FractionRing T →+* K).injective
  have hlifts : p ∈ Polynomial.lifts (algebraMap T B) :=
    (Polynomial.lifts_iff_coeff_lifts p).mpr fun n => ⟨⟨p.coeff n, hcoeff n⟩, rfl⟩
  obtain ⟨q, hqp, -, hqmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hp
  let y : FractionRing T := algebraMap T (FractionRing T) ⟨a, ha⟩ / algebraMap T (FractionRing T) ⟨b, hbS⟩
  have hφy : φ y = algebraMap B K a / algebraMap B K b := by
    simp only [y, map_div₀, hφ, IsFractionRing.lift_algebraMap]
    rfl
  have hy : IsIntegral T y := by
    refine ⟨q, hqmonic, hφinj ?_⟩
    rw [map_zero]
    change (φ : FractionRing T →+* K) (Polynomial.eval₂ (algebraMap T (FractionRing T)) y q) = 0
    rw [Polynomial.hom_eval₂, AlgHom.comp_algebraMap, RingHom.coe_coe, hφy,
      IsScalarTower.algebraMap_eq T B K, ← Polynomial.eval₂_map, hqp]
    apply hpx
  obtain ⟨t, ht⟩ := (isIntegrallyClosed_iff (FractionRing T)).mp (hS i) hy
  refine ⟨(t : B), ?_⟩
  rw [← hφy, ← ht, hφ, IsFractionRing.lift_algebraMap, IsScalarTower.algebraMap_apply T B K]
  rfl


-- created on 2026-10-20
