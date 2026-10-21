import Mathlib
import sympy.Basic
open AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma forall_mul_mem_map_imp
  {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (M : Submonoid R) [IsLocalization M S]
  (I : Ideal R) (t : R)
  -- given
  (hsat : ∀ s : R, t * s ∈ I → s ∈ I) :
  -- imply
  ∀ r : S, algebraMap R S t * r ∈ I.map (algebraMap R S) → r ∈ I.map (algebraMap R S) := by
  -- proof
  intro r hr
  obtain ⟨⟨a, m⟩, hr'⟩ := IsLocalization.surj M r
  have hta : algebraMap R S (t * a) ∈ I.map (algebraMap R S) := by
    rw [map_mul, ← hr', ← mul_assoc]
    apply Ideal.mul_mem_right _ _ hr
  obtain ⟨⟨b, n⟩, hb⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hta
  have hb' : algebraMap R S (t * a * n) = algebraMap R S b := by
    rw [← map_mul] at hb
    apply hb
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists M S).mp hb'
  have hmem : (c : R) * (n : R) * a ∈ I := by
    apply hsat
    have : t * ((c : R) * (n : R) * a) = (c : R) * (t * a * (n : R)) := by
      ring
    rw [this, hc]
    apply Ideal.mul_mem_left _ _ b.2
  have hu : IsUnit (algebraMap R S ((c : R) * (n : R) * (m : R))) := IsLocalization.map_units S ⟨_, Submonoid.mul_mem _ (Submonoid.mul_mem _ c.2 n.2) m.2⟩
  have key : r * algebraMap R S ((c : R) * (n : R) * (m : R)) = algebraMap R S ((c : R) * (n : R) * a) := by
    rw [map_mul, ← mul_assoc, mul_comm r, mul_assoc, hr', ← map_mul]
  have : r = algebraMap R S ((c : R) * (n : R) * a) * ↑(hu.unit⁻¹) := by
    rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [this]
  apply Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hmem)

/--
[AlgebraicGeometry_Scheme_IdealSheafData_forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_forall_germ_mul_mem_map_imp_and_germ_mem_nonZeroDivisors_of_forall_mul_mem_imp.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (I : X.IdealSheafData) (U : X.affineOpens) (x : ↥X) (t : X.presheaf.obj (op (U : X.Opens)))
  -- given
  (hx : x ∈ (U : X.Opens))
  (hsat : ∀ s : X.presheaf.obj (op (U : X.Opens)), t * s ∈ I.ideal U → s ∈ I.ideal U)
  (ht : t ∈ nonZeroDivisors (X.presheaf.obj (op (U : X.Opens)))) :
  -- imply
  (∀ r : X.presheaf.stalk x, X.presheaf.germ (U : X.Opens) x hx t * r ∈ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom → r ∈ (I.ideal U).map (X.presheaf.germ (U : X.Opens) x hx).hom) ∧ X.presheaf.germ (U : X.Opens) x hx t ∈ nonZeroDivisors (X.presheaf.stalk x) := by
  -- proof
  classical
  let alg : Algebra (X.presheaf.obj (op (U : X.Opens))) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  let hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (U.2.primeIdealOf ⟨x, hx⟩).asIdeal := U.2.isLocalization_stalk ⟨x, hx⟩
  have halg : algebraMap (X.presheaf.obj (op (U : X.Opens))) (X.presheaf.stalk x) = (X.presheaf.germ (U : X.Opens) x hx).hom := rfl
  refine ⟨?_, ?_⟩
  ·
    intro r hr
    have := forall_mul_mem_map_imp (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (I.ideal U) t hsat r
    rw [halg] at this
    apply this hr
  ·
    have := IsLocalization.nonZeroDivisors_le_comap (M := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) (S := X.presheaf.stalk x) ht
    rw [Submonoid.mem_comap, halg] at this
    apply this


-- created on 2026-10-20
