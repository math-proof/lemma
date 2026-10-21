import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {σ : Type*} {R : Type*} [CommRing R] (I : Ideal R)
private noncomputable def redC : MvPowerSeries σ R →ₐ[R] MvPowerSeries σ (R ⧸ I) :=
  MvPowerSeries.mapAlgHom (Ideal.Quotient.mkₐ R I)
private lemma redC_apply (p : MvPowerSeries σ R) :
    redC I p = MvPowerSeries.map (Ideal.Quotient.mk I) p := rfl
private lemma coeff_redC (p : MvPowerSeries σ R) (m : σ →₀ ℕ) :
    MvPowerSeries.coeff m (redC I p) = Ideal.Quotient.mk I (MvPowerSeries.coeff m p) :=
  MvPowerSeries.coeff_map _ _ _
private lemma redC_surjective : Function.Surjective (redC (σ := σ) I) := by
  intro q
  refine ⟨fun m => (Ideal.Quotient.mk_surjective (MvPowerSeries.coeff m q)).choose, ?_⟩
  ext m
  rw [coeff_redC]
  exact (Ideal.Quotient.mk_surjective (MvPowerSeries.coeff m q)).choose_spec
private lemma mem_ker_redC_iff (p : MvPowerSeries σ R) :
    p ∈ RingHom.ker (redC (σ := σ) I) ↔ ∀ m, MvPowerSeries.coeff m p ∈ I := by
  rw [RingHom.mem_ker, MvPowerSeries.ext_iff]
  simp only [coeff_redC, MvPowerSeries.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
private lemma map_C_le_ker_redC : I.map (MvPowerSeries.C (σ := σ) (R := R)) ≤ RingHom.ker (redC I) := by
  classical
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  rw [Ideal.mem_comap, mem_ker_redC_iff]
  intro m
  rw [MvPowerSeries.coeff_C]
  split_ifs
  exacts [hr, I.zero_mem]
private lemma ker_redC_eq_map_C (hI : I.FG) :
    RingHom.ker (redC (σ := σ) I) = I.map (MvPowerSeries.C (σ := σ) (R := R)) := by
  refine le_antisymm ?_ (map_C_le_ker_redC I)
  intro p hp
  rw [mem_ker_redC_iff] at hp
  obtain ⟨s, hs⟩ := hI
  have key : ∀ m, ∃ c : s → R, ∑ i, c i * ((↑) : s → R) i = MvPowerSeries.coeff m p := by
    intro m
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [Subtype.range_coe_subtype, Finset.setOf_mem, hs]
    exact hp m
  choose c hc using key
  have hp' : p = ∑ i : s, MvPowerSeries.C (i : R) * (show MvPowerSeries σ R from fun m => c m i) := by
    ext m
    rw [map_sum, ← hc m]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coeff_C_mul, mul_comm]
    rfl
  rw [hp']
  refine sum_mem fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  rw [← hs]
  exact Ideal.subset_span i.2
private noncomputable def quotMapCAlgEquiv (hI : I.FG) :
    (MvPowerSeries σ R ⧸ I.map (MvPowerSeries.C (σ := σ) (R := R))) ≃ₐ[R]
      MvPowerSeries σ (R ⧸ I) :=
  (Ideal.quotientEquivAlgOfEq R (ker_redC_eq_map_C I hI).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (redC_surjective I))
private lemma quotMapCAlgEquiv_mk (hI : I.FG) (p : MvPowerSeries σ R) :
    quotMapCAlgEquiv I hI (Ideal.Quotient.mk _ p) = MvPowerSeries.map (Ideal.Quotient.mk I) p := by
  rw [quotMapCAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk, redC_apply]
/--
[MvPowerSeries_exists_algEquiv_quotient_map_C](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MvPowerSeries_exists_algEquiv_quotient_map_C.lean)
-/
@[path]
private lemma main {σ : Type u} {R : Type v} [CommRing R]
    (I : Ideal R) (hI : I.FG) :
    ∃ e : (MvPowerSeries σ R ⧸ I.map (MvPowerSeries.C (σ := σ) (R := R))) ≃ₐ[R]
        MvPowerSeries σ (R ⧸ I),
      ∀ p : MvPowerSeries σ R,
        e (Ideal.Quotient.mk (I.map (MvPowerSeries.C (σ := σ) (R := R))) p) =
          MvPowerSeries.map (Ideal.Quotient.mk I) p :=
  ⟨quotMapCAlgEquiv I hI, quotMapCAlgEquiv_mk I hI⟩

-- created on 2026-10-20
