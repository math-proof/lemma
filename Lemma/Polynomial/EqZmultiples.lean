import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_Affine_Point_zmultiples_eq_of_forall_isRoot_iff_of_addOrderOf_eq.lean)
-/
@[path]
private lemma main
  (Ω : Type) [Field Ω] [DecidableEq Ω] (W : WeierstrassCurve Ω) (M' : ℕ) [NeZero M']
  (H : AddSubgroup W.toAffine.Point) (hH : IsAddCyclic H ∧ Nat.card H = M')
  (h : ↥M'.primeFactors → Polynomial Ω) (_ : ∀ p, h p ≠ 0)
  (hroots : ∀ (p : ↥M'.primeFactors) (x₁ : Ω),
    (h p).IsRoot x₁ ↔ ∃ (P : W.toAffine.Point) (y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
      P ∈ H ∧ addOrderOf P = (p : ℕ) ^ M'.factorization (p : ℕ) ∧ P = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁)
  (g : W.toAffine.Point)
  (hg : addOrderOf g = M' ∧
    ∀ (p : ↥M'.primeFactors) (n : ℕ) (x₁ y₁ : Ω) (h₁ : W.toAffine.Nonsingular x₁ y₁),
      n • g = WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ → addOrderOf (n • g) = (p : ℕ) ^ M'.factorization (p : ℕ) →
      (h p).IsRoot x₁) :
  -- imply
  AddSubgroup.zmultiples g = H := by
  -- proof
  classical
  obtain ⟨hord, hcut⟩ := hg
  have hM0 : M' ≠ 0 := NeZero.ne M'
  have hcardH : Nat.card H ≠ 0 := by
    rw [hH.2]
    refine hM0
  let hHfin : Finite H := Nat.finite_of_card_ne_zero hcardH
  have hcardG : Nat.card (AddSubgroup.zmultiples g) = M' := by
    rw [Nat.card_zmultiples, hord]
  have hcardG0 : Nat.card (AddSubgroup.zmultiples g) ≠ 0 := by
    rw [hcardG]
    refine hM0
  let hGfin : Finite (AddSubgroup.zmultiples g) := Nat.finite_of_card_ne_zero hcardG0
  have key : ∀ p : ↥M'.primeFactors,
      addOrderOf ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) = (p : ℕ) ^ M'.factorization (p : ℕ) ∧
        (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g ∈ H := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hpk : (p : ℕ) ^ M'.factorization (p : ℕ) ∣ M' := Nat.ordProj_dvd M' p
    have hordp : addOrderOf ((M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g) =
        (p : ℕ) ^ M'.factorization (p : ℕ) := by
      have hn0 : M' / (p : ℕ) ^ M'.factorization (p : ℕ) ≠ 0 :=
        (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hpk) (pow_pos hp.pos _)).ne'
      have hdivg : M' / (p : ℕ) ^ M'.factorization (p : ℕ) ∣ addOrderOf g := by
        rw [hord]
        refine Nat.div_dvd_of_dvd hpk
      rw [addOrderOf_nsmul_of_dvd hn0 hdivg, hord, Nat.div_div_self hpk hM0]
    refine ⟨hordp, ?_⟩
    have hk : 0 < M'.factorization (p : ℕ) := hp.factorization_pos_of_dvd hM0 (Nat.dvd_of_mem_primeFactors p.2)
    have hne : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g ≠ 0 := by
      intro h0'
      rw [h0', addOrderOf_zero] at hordp
      have : 1 < (p : ℕ) ^ M'.factorization (p : ℕ) := Nat.one_lt_pow hk.ne' hp.one_lt
      omega
    cases hgp : (M' / (p : ℕ) ^ M'.factorization (p : ℕ)) • g
    · refine absurd hgp hne
    ·
      rename_i x₁ y₁ h₁
      have hroot : (h p).IsRoot x₁ := hcut p _ x₁ y₁ h₁ hgp hordp
      obtain ⟨P, y₂, h₂, hPH, _, hPeq⟩ := (hroots p x₁).mp hroot
      cases WeierstrassCurve.Affine.Y_eq_of_X_eq h₂.left h₁.left rfl
      ·
        rename_i hy
        subst hy
        rw [hPeq] at hPH
        refine hPH
      ·
        rename_i hy
        subst hy
        have hneg : P = -WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ := by
          rw [hPeq, WeierstrassCurve.Affine.Point.neg_some]
        have := H.neg_mem hPH
        rw [hneg, neg_neg] at this
        refine this
  set I : AddSubgroup W.toAffine.Point := AddSubgroup.zmultiples g ⊓ H with hI
  let hIfin : Finite I :=
    Finite.of_injective (AddSubgroup.inclusion (inf_le_right : I ≤ H)) (AddSubgroup.inclusion_injective _)
  have hIpos : 0 < Nat.card I := Nat.card_pos
  have hdiv : M' ∣ Nat.card I := by
    rw [← Nat.factorization_le_iff_dvd hM0 hIpos.ne', Finsupp.le_def]
    intro p
    if hp : p ∈ M'.primeFactors then
      obtain ⟨hordp, hmemH⟩ := key ⟨p, hp⟩
      have hmem : (M' / p ^ M'.factorization p) • g ∈ I :=
        ⟨AddSubgroup.nsmul_mem _ (AddSubgroup.mem_zmultiples g) _, hmemH⟩
      have hd := AddSubgroup.addOrderOf_dvd_natCard I hmem
      rw [hordp] at hd
      refine ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hIpos.ne').mp hd
    else
      rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hp
      rw [hp]
      refine Nat.zero_le _
  have hleG : Nat.card (AddSubgroup.zmultiples g) ≤ Nat.card I := by
    rw [hcardG]
    refine Nat.le_of_dvd hIpos hdiv
  have hIG : I = AddSubgroup.zmultiples g :=
    AddSubgroup.eq_of_le_of_card_ge inf_le_left hleG
  have hleH : Nat.card H ≤ Nat.card I := by
    rw [hH.2]
    refine Nat.le_of_dvd hIpos hdiv
  have hIH : I = H :=
    AddSubgroup.eq_of_le_of_card_ge inf_le_right hleH
  refine hIG.symm.trans hIH


-- created on 2026-10-20
