import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing Polynomial


private lemma monic_splits_of_isAlgClosed_frac {R : Type*} [CommRing R] [IsDomain R]
  [IsIntegrallyClosed R] {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  [IsAlgClosed K] {p : R[X]} (hp : p.Monic) : p.Splits := by
  have hφ := IsFractionRing.injective R K
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
  obtain rfl | hn0 := Nat.eq_zero_or_pos n
  ·
    rw [hp.natDegree_eq_zero.mp hn]; exact .one
  have hdeg : (p.map (algebraMap R K)).degree ≠ 0 := by
    rw [degree_eq_natDegree (hp.map _).ne_zero, hp.natDegree_map, hn]
    exact_mod_cast hn0.ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hαint : IsIntegral R α := ⟨p, hp, by
    rwa [show eval₂ (algebraMap R K) α p = eval α (p.map (algebraMap R K)) from
      (eval_map _ _).symm]⟩
  obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hαint
  have haroot : p.IsRoot a := by
    refine IsRoot.def.mpr (hφ ?_)
    rwa [← eval₂_at_apply, ← eval_map, ha, map_zero]
  have hpeel : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr haroot
  have hQmonic : (p /ₘ (X - C a)).Monic := by
    apply (monic_X_sub_C a).of_mul_monic_left; rwa [hpeel]
  have hQdeg : (p /ₘ (X - C a)).natDegree = n - 1 := by
    rw [natDegree_divByMonic p (monic_X_sub_C a), natDegree_X_sub_C, hn]
  rw [← hpeel]
  exact (Splits.X_sub_C a).mul (ih (n - 1) (Nat.sub_lt hn0 one_pos) hQmonic hQdeg)

private lemma exists_algHom_residue_eq_of_finite_flat_valuationRing
  {R : Type*} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
  {H : Type*} [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Flat R H]
  (φ : H →ₐ[R] ResidueField R) :
  ∃ ψ : H →ₐ[R] R, ∀ h, residue R (ψ h) = φ h := by
  classical
  let m : Ideal H := RingHom.ker φ
  have hm_prime : m.IsPrime := RingHom.ker_isPrime φ
  have hm_under : Ideal.under R m = maximalIdeal R := by
    ext a; rw [Ideal.mem_comap, RingHom.mem_ker, φ.commutes]; exact residue_eq_zero_iff a
  obtain ⟨q, hq_le, hq_prime, hq_under⟩ :
    ∃ q ≤ m, q.IsPrime ∧ Ideal.under R q = (⊥ : Ideal R) := by
    obtain h | h := eq_or_lt_of_le (bot_le : ⊥ ≤ Ideal.under R m)
    · exact ⟨m, le_refl m, hm_prime, h.symm⟩
    ·
      obtain ⟨q, hle, hp, hover⟩ :=
        Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (R := R) m h
      exact ⟨q, hle, hp, hover.over.symm⟩
  have := hq_prime
  have hRinj : Function.Injective (algebraMap R (H ⧸ q)) := by
    rwa [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq R H (H ⧸ q),
      Ideal.Quotient.algebraMap_eq, ← RingHom.comap_ker, Ideal.mk_ker]
  have : IsDomain (H ⧸ q) := Ideal.Quotient.isDomain q
  have : Module.Finite R (H ⧸ q) := .of_surjective
    (Ideal.Quotient.mkₐ R q).toLinearMap Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral R (H ⧸ q) := .of_finite R _
  have hRsurj : Function.Surjective (algebraMap R (H ⧸ q)) := by
    intro b
    obtain ⟨p, hp_monic, hp_eval⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    have hp_splits : p.Splits := monic_splits_of_isAlgClosed_frac (K := K) hp_monic
    have hb_root : (p.map (algebraMap R (H ⧸ q))).IsRoot b := by
      rwa [IsRoot, eval_map]
    have hroots : (p.map (algebraMap R (H ⧸ q))).roots = p.roots.map (algebraMap R (H ⧸ q)) :=
      (roots_map_of_injective_of_card_eq_natDegree hRinj
        (splits_iff_card_roots.mp hp_splits)).symm
    have hb_mem : b ∈ (p.map (algebraMap R (H ⧸ q))).roots :=
      (mem_roots (hp_monic.map _).ne_zero).mpr hb_root
    rw [hroots, Multiset.mem_map] at hb_mem
    obtain ⟨r, _, hr⟩ := hb_mem
    exact ⟨r, hr⟩
  let e : R ≃ₐ[R] (H ⧸ q) := AlgEquiv.ofBijective (Algebra.ofId R (H ⧸ q)) ⟨hRinj, hRsurj⟩
  let ψ : H →ₐ[R] R := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ R q)
  refine ⟨ψ, fun h ↦ ?_⟩
  let φbar : (H ⧸ q) →ₐ[R] ResidueField R := Ideal.Quotient.liftₐ q φ
    (fun a ha ↦ by have := hq_le ha; rwa [RingHom.mem_ker] at this)
  have heq : ∀ x : H ⧸ q, algebraMap R (H ⧸ q) (e.symm x) = x := fun x ↦ e.apply_symm_apply x
  calc
    _ = algebraMap R (ResidueField R) (e.symm (Ideal.Quotient.mk q h)) := rfl
    _ = φbar (algebraMap R (H ⧸ q) (e.symm (Ideal.Quotient.mk q h))) := (φbar.commutes _).symm
    _ = φbar (Ideal.Quotient.mk q h) := by rw [heq]
    _ = φ h := rfl
/--
[ValuationRing_exists_algHom_lift_residue_of_finite_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationRing_exists_algHom_lift_residue_of_finite_flat.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K] [CommRing H] [Algebra R H] [Module.Finite R H] [Module.Flat R H]
  {φ : H →ₐ[R] IsLocalRing.ResidueField R} :
-- imply
  ∃ ψ : H →ₐ[R] R, ∀ h, IsLocalRing.residue R (ψ h) = φ h :=
-- proof
  exists_algHom_residue_eq_of_finite_flat_valuationRing (K := K) φ


-- created on 2026-10-23
