import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise


/--
[MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MulSemiringAction_mem_of_forall_smul_sub_mem_and_exists_forall_smul_sub_mem_of_forall_sup_smul_eq_top.lean)
-/
@[path]
private lemma main
  [CommRing B] [Group G] [Finite G] [MulSemiringAction G B]
  {I P : Ideal B}
-- given
  (hIP : I ≤ P)
  (hI : ∀ (g : G) (b : B), b ∈ I → g • b ∈ I)
  (hmax : ∀ g : G, g • P ≠ P → P ⊔ g • P = ⊤)
  (hinf : ∀ b : B, (∀ g : G, g • b ∈ P) → b ∈ I) :
-- imply
  (∀ b : B, (∀ g : G, g • b - b ∈ I) → b ∈ P → b ∈ I) ∧
    (∀ s : B, (∀ g : G, g • P = P → g • s - s ∈ P) →
      ∃ r : B, (∀ g : G, g • r - r ∈ I) ∧ r - s ∈ P) := by
-- proof
  classical
    refine ⟨?_, ?_⟩
    ·
      intro b hb hbP
      apply hinf
      intro g
      have : g • b = (g • b - b) + b := by abel
      rw [this]
      exact P.add_mem (hIP (hb g)) hbP
    ·
      intro s hs
      let ι : Type _ := ↥(Set.range fun g : G => g • P)
      have hch : ∀ Q : ι, ∃ g : G, g • P = Q.1 := fun Q => Q.2
      choose gsel hgsel using hch
      have hall : ∀ b : B, (∀ Q : ι, b ∈ Q.1) → b ∈ I := by
        intro b hb
        apply hinf
        intro h
        rw [← Ideal.mem_inv_pointwise_smul_iff]
        apply hb ⟨h⁻¹ • P, h⁻¹, rfl⟩
      have hcop : Pairwise (Function.onFun IsCoprime fun Q : ι => Q.1) := by
        intro Q Q' hne
        change IsCoprime Q.1 Q'.1
        rw [Ideal.isCoprime_iff_sup_eq, ← hgsel Q, ← hgsel Q']
        have hne' : ((gsel Q)⁻¹ * gsel Q') • P ≠ P := by
          intro h
          apply hne
          apply Subtype.ext
          rw [← hgsel Q, ← hgsel Q']
          calc
            _ = gsel Q • (((gsel Q)⁻¹ * gsel Q') • P) := by rw [h]
            _ = gsel Q' • P := by rw [smul_smul, mul_inv_cancel_left]
        have h1 := hmax _ hne'
        calc
          _ = gsel Q • (P ⊔ ((gsel Q)⁻¹ * gsel Q') • P) := by
          rw [Ideal.smul_sup, smul_smul, mul_inv_cancel_left]
          _ = ⊤ := by rw [h1, ← Ideal.one_eq_top, smul_one]
      obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal hcop (fun Q : ι => gsel Q • s)
      have key : ∀ (g : G) (Q : ι), g • r - r ∈ Q.1 := by
        intro g Q
        let Q' : ι := ⟨g⁻¹ • Q.1, g⁻¹ * gsel Q, by show (g⁻¹ * gsel Q) • P = g⁻¹ • Q.1; rw [mul_smul, hgsel Q]⟩
        have h1 : g • r - (g * gsel Q') • s ∈ Q.1 := by
          have := Ideal.smul_mem_pointwise_smul g _ _ (hr Q')
          have hQ : g • (Q'.1) = Q.1 := by
            change g • (g⁻¹ • Q.1) = Q.1
            rw [smul_inv_smul]
          rwa [hQ, smul_sub, ← mul_smul] at this
        have hstab : ((gsel Q)⁻¹ * (g * gsel Q')) • P = P := by
          rw [mul_smul, mul_smul, hgsel Q']
          change (gsel Q)⁻¹ • g • (g⁻¹ • Q.1) = P
          rw [smul_inv_smul, ← hgsel Q, inv_smul_smul]
        have h2 : (g * gsel Q') • s - gsel Q • s ∈ Q.1 := by
          have := Ideal.smul_mem_pointwise_smul (gsel Q) _ _ (hs _ hstab)
          rwa [smul_sub, smul_smul, mul_inv_cancel_left, hgsel Q] at this
        have h3 := hr Q
        have : g • r - r = (g • r - (g * gsel Q') • s) + ((g * gsel Q') • s - gsel Q • s) - (r - gsel Q • s) := by
          abel
        rw [this]
        apply Q.1.sub_mem (Q.1.add_mem h1 h2) h3
      refine ⟨r, fun g => hall _ (key g), ?_⟩
      let Q₀ : ι := ⟨P, 1, one_smul _ _⟩
      have h1 := hr Q₀
      have h2 : gsel Q₀ • s - s ∈ P := hs _ (hgsel Q₀)
      have : r - s = (r - gsel Q₀ • s) + (gsel Q₀ • s - s) := by abel
      rw [this]
      exact P.add_mem h1 h2


-- created on 2026-10-23
