import Mathlib
import sympy.Basic
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


abbrev LtPair (m : ℕ) : Type := Subtype fun p : Fin m × Fin m => p.1 < p.2
private lemma card_ltPairs (m : ℕ) : Fintype.card (LtPair m) = m.choose 2 := by
  classical
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type, Finset.sum_comm]
  have h1 : ∀ j : Fin m, (∑ i : Fin m, if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  simp_rw [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) m, Finset.sum_range_id, Nat.choose_two_right]
private noncomputable def kvec {R : Type} [CommRing R] {m : ℕ} (σ : Fin m → R) (q : Fin m × Fin m) : Fin m → R :=
  Pi.single q.1 (σ q.2) - Pi.single q.2 (σ q.1)
private lemma kvec_mem_ker {R : Type} [CommRing R] {m : ℕ} (σ : Fin m → R) (q : Fin m × Fin m) : kvec σ q ∈ LinearMap.ker (Fintype.linearCombination R σ) := by
  classical
  rw [LinearMap.mem_ker, kvec, map_sub, Fintype.linearCombination_apply_single, Fintype.linearCombination_apply_single, smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
private lemma sum_kvec_apply {R : Type} [CommRing R] {m : ℕ} (σ : Fin m → R) (c : Fin m → Fin m → R) (k : Fin m) : (∑ q : Fin m × Fin m, c q.1 q.2 • kvec σ q) k = ∑ l, (c k l - c l k) * σ l := by
  classical
  rw [Finset.sum_apply]
  simp only [kvec, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, smul_eq_mul, mul_sub, mul_ite, mul_zero]
  rw [Finset.sum_sub_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl fun l _ => (sub_mul _ _ _).symm
private lemma helper_main {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (σ : Fin m → R) (hσ : ∀ c : Fin m → R, ∑ i, c i * σ i ∈ maximalIdeal R ^ 2 → ∀ i, c i ∈ maximalIdeal R) {ρ : ℕ} (η : Module.Basis (Fin ρ) R (LinearMap.ker (Fintype.linearCombination R σ))) : m.choose 2 ≤ ρ := by
  classical
  set K := LinearMap.ker (Fintype.linearCombination R σ) with hKdef
  set 𝔪 := maximalIdeal R with h𝔪
  let κ : Type := R ⧸ 𝔪
  let _ : Nontrivial κ := Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsMaximal.ne_top inferInstance)
  have hK : ∀ v : K, ∀ i, (v : Fin m → R) i ∈ 𝔪 := by
    intro v i
    apply hσ
    have hv := v.2
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hv
    simp only [smul_eq_mul] at hv
    rw [hv]
    apply Submodule.zero_mem _
  have hmK : ∀ w : K, w ∈ (𝔪 • ⊤ : Submodule R K) → ∀ i, (w : Fin m → R) i ∈ 𝔪 ^ 2 := by
    intro w hw
    refine Submodule.smul_induction_on (p := fun w : K => ∀ i, (w : Fin m → R) i ∈ 𝔪 ^ 2) hw ?_ ?_
    ·
      intro r hr n _ i
      rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, pow_two]
      apply Ideal.mul_mem_mul hr (hK n i)
    ·
      intro x y hx hy i
      rw [Submodule.coe_add, Pi.add_apply]
      apply Ideal.add_mem _ (hx i) (hy i)
  let kv : LtPair m → K := fun p => ⟨kvec σ p.1, kvec_mem_ker σ p.1⟩
  have hkv : ∀ p : LtPair m, ((kv p : K) : Fin m → R) = kvec σ p.1 := fun p => rfl
  let fam : LtPair m → κ ⊗[R] K := fun p => (1 : κ) ⊗ₜ[R] kv p
  have hli : LinearIndependent κ fam := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p₀
    obtain ⟨G, hG⟩ : ∃ G : LtPair m → R, ∀ p, Ideal.Quotient.mk 𝔪 (G p) = g p := ⟨fun p => (Ideal.Quotient.mk_surjective (g p)).choose, fun p => (Ideal.Quotient.mk_surjective (g p)).choose_spec⟩
    set w : K := ∑ p, G p • kv p with hw
    have h1w : (1 : κ) ⊗ₜ[R] w = 0 := by
      rw [hw, TensorProduct.tmul_sum, ← hg]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← hG p, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, TensorProduct.tmul_smul]
    have hwmem : w ∈ (𝔪 • ⊤ : Submodule R K) := by
      have h := congrArg (TensorProduct.quotTensorEquivQuotSMul K 𝔪) h1w
      rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, LinearEquiv.map_zero, Submodule.Quotient.mk_eq_zero] at h
      apply h
    have hcoord := hmK w hwmem
    let c : Fin m → Fin m → R := fun i j => if h : i < j then G ⟨(i, j), h⟩ else 0
    have hwc : (w : Fin m → R) = ∑ q : Fin m × Fin m, c q.1 q.2 • kvec σ q := by
      rw [hw, Submodule.coe_sum]
      simp only [Submodule.coe_smul, hkv]
      have hGc : ∀ p : LtPair m, G p • kvec σ p.1 = (fun q : Fin m × Fin m => c q.1 q.2 • kvec σ q) p.1 := by
        intro p
        obtain ⟨⟨i, j⟩, hij⟩ := p
        simp only [c, dite_eq_left hij]
      calc
        _ = ∑ p : LtPair m, (fun q : Fin m × Fin m => c q.1 q.2 • kvec σ q) p.1 := Finset.sum_congr rfl fun p _ => hGc p
        _ = ∑ q ∈ Finset.univ.filter (fun q : Fin m × Fin m => q.1 < q.2), (fun q : Fin m × Fin m => c q.1 q.2 • kvec σ q) q := (Finset.sum_subtype (p := fun q : Fin m × Fin m => q.1 < q.2) (Finset.univ.filter fun q : Fin m × Fin m => q.1 < q.2) (fun q => by simp) (fun q : Fin m × Fin m => c q.1 q.2 • kvec σ q)).symm
        _ = ∑ q, c q.1 q.2 • kvec σ q := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun q _ => ?_
          if hq : q.1 < q.2 then
            simp only [ite_eq_left hq]
          else
            simp only [ite_eq_right hq, c, dite_eq_right hq, zero_smul]
    obtain ⟨⟨k, l⟩, hkl⟩ := p₀
    have hk : (w : Fin m → R) k = ∑ j, (c k j - c j k) * σ j := by
      rw [hwc, sum_kvec_apply]
    have hmem := hσ (fun j => c k j - c j k) (hk ▸ hcoord k) l
    have hc1 : c k l = G ⟨(k, l), hkl⟩ := by simp only [c, dite_eq_left hkl]
    have hc2 : c l k = 0 := by simp only [c, dite_eq_right (not_lt.mpr hkl.le)]
    simp only [hc1, hc2, sub_zero] at hmem
    rw [← hG]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  let β := Algebra.TensorProduct.basis κ η
  let _ : Module.Finite κ (κ ⊗[R] K) := Module.Finite.of_basis β
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_eq_card_basis β, Fintype.card_fin] at hle
  simpa only [card_ltPairs] using hle
/--
[IsLocalRing_choose_two_le_of_basis_ker_linearCombination](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_choose_two_le_of_basis_ker_linearCombination.lean)
-/
@[path]
private lemma main
  {R : Type} {m ρ : ℕ} [CommRing R] [IsLocalRing R]
  (σ : Fin m → R)
  (η : Module.Basis (Fin ρ) R (LinearMap.ker (Fintype.linearCombination R σ)))
  -- given
  (hσ : ∀ c : Fin m → R, ∑ i, c i * σ i ∈ maximalIdeal R ^ 2 → ∀ i, c i ∈ maximalIdeal R) :
  -- imply
  m.choose 2 ≤ ρ :=
  helper_main σ hσ η


-- created on 2026-10-20
