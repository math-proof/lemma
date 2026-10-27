import Mathlib
import Initialize.Tactic.Attr.Basic
open Algebra.FormallyUnramified
open scoped TensorProduct


private noncomputable def phi
  [CommRing R] [CommRing S] [Algebra R S]
  (σ : S →ₐ[R] S) : S ⊗[R] S →ₐ[R] S :=
  Algebra.TensorProduct.productMap (AlgHom.id R S) σ


private lemma exists_fin_sum_tmul
  [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
  (z : M ⊗[R] N) :
-- imply
  ∃ (n : ℕ) (x : Fin n → M) (y : Fin n → N), z = ∑ i, x i ⊗ₜ[R] y i := by
-- proof
  obtain ⟨s, hs⟩ := TensorProduct.exists_finset z
  refine ⟨s.card, fun i => (s.equivFin.symm i).1.1, fun i => (s.equivFin.symm i).1.2, ?_⟩
  rw [hs, ← Finset.sum_coe_sort]
  apply Fintype.sum_equiv s.equivFin _ _ (fun p => by simp)


private lemma phi_tmul
  [CommRing R] [CommRing S] [Algebra R S]
  (σ : S →ₐ[R] S) (a b : S) :
-- imply
  phi σ (a ⊗ₜ[R] b) = a * σ b := rfl


private lemma phi_apply_of_forall_eq
  [CommRing R] [CommRing S] [Algebra R S]
  (σ : S →ₐ[R] S) {z : S ⊗[R] S}
-- given
  (h : ∀ a, σ a = a) :
-- imply
  phi σ z = Algebra.TensorProduct.lmul' R (S := S) z := by
-- proof
  induction z using TensorProduct.inductionOn with
  | tmul a b =>
    rw [phi_tmul, Algebra.TensorProduct.lmul'_apply_tmul, h]
  | add u v hu hv =>
    rw [map_add, map_add, hu, hv]


private lemma mul_elem_eq
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
  (x : S ⊗[R] S) :
-- imply
  x * elem R S = (Algebra.TensorProduct.lmul' R (S := S) x ⊗ₜ[R] (1 : S)) * elem R S := by
-- proof
  induction x using TensorProduct.inductionOn with
  | tmul a b =>
    rw [Algebra.TensorProduct.lmul'_apply_tmul]
    have hab : a ⊗ₜ[R] b = (a ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hab, mul_assoc, one_tmul_mul_elem, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | add u v hu hv =>
    rw [add_mul, hu, hv, map_add, TensorProduct.add_tmul, add_mul]


private lemma isIdempotentElem_elem
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
-- imply
  IsIdempotentElem (elem R S) := by
-- proof
  show elem R S * elem R S = elem R S
  rw [mul_elem_eq, lmul_elem, ← Algebra.TensorProduct.one_def, one_mul]


private lemma sub_mul_phi_elem
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
  (σ : S →ₐ[R] S) (a : S) :
-- imply
  (σ a - a) * phi σ (elem R S) = 0 := by
-- proof
  have h := congrArg (phi σ) (one_tmul_sub_tmul_one_mul_elem (R := R) (S := S) a)
  rw [map_mul, map_zero, map_sub, phi_tmul, phi_tmul] at h
  simp at h
  apply h


private lemma phi_elem_eq_zero_or_forall_eq
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
  [IsLocalRing S]
  (σ : S →ₐ[R] S) :
-- imply
  phi σ (elem R S) = 0 ∨ ∀ a, σ a = a := by
-- proof
  have hidem : IsIdempotentElem (phi σ (elem R S)) := isIdempotentElem_elem.map (phi σ)
  obtain hu | hu := IsLocalRing.isUnit_or_isUnit_one_sub_self (phi σ (elem R S))
  ·
    have he1 : phi σ (elem R S) = 1 := hu.mul_left_cancel (hidem.eq.trans (mul_one _).symm)
    refine Or.inr ?_
    intro a
    have h := sub_mul_phi_elem σ a
    rwa [he1, mul_one, sub_eq_zero] at h
  ·
    refine Or.inl ?_
    apply hu.mul_left_eq_zero.mp
    rw [mul_sub, mul_one, hidem.eq, sub_self]


private lemma phi_elem_eq_one_of_forall_eq
  [CommRing R] [CommRing S] [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
  (σ : S →ₐ[R] S)
-- given
  (h : ∀ a, σ a = a) :
-- imply
  phi σ (elem R S) = 1 := by
-- proof
  rw [phi_apply_of_forall_eq σ h, lmul_elem]


private lemma finrank_mul_finrank_le
  [CommRing W] [Nontrivial W] [CommRing W'] [Algebra W W'] [Module.Free W W'] [Module.Finite W W']
  [Group G] [Fintype G] [DecidableEq G]
  (ρ : G →* (W' ≃ₐ[W] W')) {n : ℕ} (x y : Fin n → W')
-- given
  (hinv : ∀ w : W', (∀ g : G, ρ g w = w) → w ∈ Set.range (algebraMap W W'))
  (hxy : ∀ g : G, ∑ i, x i * ρ g (y i) = if g = 1 then 1 else 0) :
-- imply
  Module.finrank W W' * Module.finrank W W' ≤ Fintype.card G * Module.finrank W W' := by
-- proof
  classical
  let Φ : W' ⊗[W] W' →ₗ[W] (G → W') :=
    LinearMap.pi fun g => (phi (R := W) ((ρ g : W' ≃ₐ[W] W') : W' →ₐ[W] W')).toLinearMap
  have hΦ : ∀ (a b : W') (g : G), Φ (a ⊗ₜ[W] b) g = a * ρ g b := fun _ _ _ => rfl
  let Ψ : (G → W') → W' ⊗[W] W' := fun c => ∑ i, (∑ g, c g * ρ g (x i)) ⊗ₜ[W] y i
  have hΨ : ∀ c, Ψ c = ∑ i, (∑ g, c g * ρ g (x i)) ⊗ₜ[W] y i := fun _ => rfl
  have hΨadd : ∀ c d, Ψ (c + d) = Ψ c + Ψ d := by
    intro c d
    simp [hΨ, Pi.add_apply, add_mul, Finset.sum_add_distrib, TensorProduct.add_tmul]
  have htr : ∀ w : W', ∃ r : W, algebraMap W W' r = ∑ g, ρ g w := by
    intro w
    obtain ⟨r, hr⟩ := hinv (∑ g, ρ g w) (fun h => by
      rw [map_sum]
      apply Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => by simp [map_mul, AlgEquiv.mul_apply]))
    refine ⟨r, hr⟩
  have key : ∀ g : G, ∑ i, ρ g (x i) * y i = if g = 1 then 1 else 0 := by
    intro g
    have h := congrArg (ρ g) (hxy g⁻¹)
    rw [map_sum] at h
    convert h using 1
    ·
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply]
    ·
      simp [inv_eq_one]
  have hsum : ∀ b : W', ∑ i, (∑ g, ρ g (b * x i)) * y i = b := by
    intro b
    calc
      _ = ∑ g, ρ g b * ∑ i, ρ g (x i) * y i := by
        simp [map_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
        rw [Finset.sum_comm]
      _ = b := by
        simp [key, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, map_one, AlgEquiv.one_apply]
  have hleft : Function.LeftInverse Ψ Φ := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      simp [hΨ, hΦ]
      have h1 : ∀ i, ∑ g, a * ρ g b * ρ g (x i) = a * ∑ g, ρ g (b * x i) := by
        intro i
        simp [map_mul, Finset.mul_sum, mul_assoc]
      have h2 : ∀ i, (a * ∑ g, ρ g (b * x i)) ⊗ₜ[W] y i = a ⊗ₜ[W] ((∑ g, ρ g (b * x i)) * y i) := by
        intro i
        obtain ⟨r, hr⟩ := htr (b * x i)
        rw [← hr, ← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
      simp_rw [h1, h2, ← TensorProduct.tmul_sum, hsum]
    | add u v hu hv =>
      rw [map_add, hΨadd, hu, hv]
  have hinj : Function.Injective Φ := hleft.injective
  have h := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_tensorProduct, Module.finrank_pi_fintype] at h
  simp [Finset.sum_const, Finset.card_univ] at h
  apply h


/--
[Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_Etale_exists_sum_mul_smul_eq_ite_of_isLocalRing.lean)
-/
@[path]
private lemma main
  [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
  [Algebra W W'] [Module.Finite W W'] [Module.Flat W W'] [FaithfulSMul W W'] [Algebra.Etale W W']
  [Group Γ] [Fintype Γ] [DecidableEq Γ] [MulSemiringAction Γ W'] [SMulCommClass Γ W W']
-- given
  (hinv : ∀ w' : W', (∀ γ : Γ, γ • w' = w') ↔ w' ∈ Set.range (algebraMap W W'))
  (hcard : Fintype.card Γ = Module.finrank W W') :
-- imply
  ∃ (n : ℕ) (x y : Fin n → W'), ∀ γ : Γ, ∑ i, x i * γ • y i = if γ = 1 then 1 else 0 := by
-- proof
  classical
  have : Module.Free W W' := Module.free_of_flat_of_isLocalRing
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ →* (W' ≃ₐ[W] W'), ∀ (γ : Γ) (w : W'), ρ γ w = γ • w :=
    ⟨MulSemiringAction.toAlgAut Γ W W', fun _ _ => rfl⟩
  obtain ⟨n, x, y, hε⟩ := exists_fin_sum_tmul (elem W W' : W' ⊗[W] W')
  have hc : ∀ σ : W' →ₐ[W] W', phi σ (elem W W') = ∑ i, x i * σ (y i) := by
    intro σ
    rw [hε, map_sum]
    rfl
  have hK : ∀ γ : Γ, (∑ i, x i * γ • y i) = if γ ∈ ρ.ker then 1 else 0 := by
    intro γ
    have h1 : phi ((ρ γ : W' ≃ₐ[W] W') : W' →ₐ[W] W') (elem W W') = ∑ i, x i * γ • y i := by
      rw [hc]
      simp [hρ]
    rw [← h1]
    split_ifs with hγ
    ·
      rw [MonoidHom.mem_ker] at hγ
      apply phi_elem_eq_one_of_forall_eq _ (fun a => by simp [hγ])
    ·
      obtain h0 | hfix := phi_elem_eq_zero_or_forall_eq (R := W) ((ρ γ : W' ≃ₐ[W] W') : W' →ₐ[W] W')
      · apply h0
      · apply absurd (MonoidHom.mem_ker.mpr (AlgEquiv.ext hfix)) hγ
  have hKbot : ρ.ker = ⊥ := by
    have : Fintype (Γ ⧸ ρ.ker) := Fintype.ofFinite _
    have hxy' : ∀ g : Γ ⧸ ρ.ker, ∑ i, x i * QuotientGroup.kerLift ρ g (y i) = if g = 1 then 1 else 0 := by
      intro g
      obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective g
      rw [QuotientGroup.kerLift_mk]
      simp [hρ, hK, QuotientGroup.eq_one_iff]
    have hinv' : ∀ w : W', (∀ g : Γ ⧸ ρ.ker, QuotientGroup.kerLift ρ g w = w) → w ∈ Set.range (algebraMap W W') := by
      intro w hw
      apply (hinv w).mp
      intro γ
      have h := hw (γ : Γ ⧸ ρ.ker)
      rwa [QuotientGroup.kerLift_mk, hρ] at h
    have hb := finrank_mul_finrank_le (QuotientGroup.kerLift ρ) x y hinv' hxy'
    rw [← hcard] at hb
    have h1 : Fintype.card Γ ≤ Fintype.card (Γ ⧸ ρ.ker) := Nat.le_of_mul_le_mul_right hb Fintype.card_pos
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_eq_fintype_card (α := Γ), Nat.card_eq_fintype_card (α := Γ ⧸ ρ.ker)] at h2
    have h3 : Fintype.card (Γ ⧸ ρ.ker) * Nat.card ρ.ker ≤ Fintype.card (Γ ⧸ ρ.ker) * 1 := by
      rw [mul_one, ← h2]
      apply h1
    refine Subgroup.eq_bot_of_card_le _ (Nat.le_of_mul_le_mul_left h3 Fintype.card_pos)
  refine ⟨n, x, y, fun γ => ?_⟩
  rw [hK γ]
  simp [hKbot, Subgroup.mem_bot]


-- created on 2026-10-16
