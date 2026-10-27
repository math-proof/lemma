import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma det_eq_of_dep
  {X : Type}
  {f g : X → ℂ}
  {x y : X}
  -- given
  (h : ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t, c.1 * f t + c.2 * g t = 0) :
  -- imply
  f x * g y = f y * g x := by
  -- proof
  obtain ⟨c, hc, hfg⟩ := h
  if h1 : c.1 = 0 then
    have h2 : c.2 ≠ 0 := by
      intro h2
      apply hc
      apply Prod.ext h1 h2
    have hg : ∀ t, g t = 0 := fun t => by
      have := hfg t
      rw [h1, zero_mul, zero_add] at this
      apply (Iff.mp mul_eq_zero this).resolve_left h2
    simp [hg]
  else
    have hf : ∀ t, f t = -(c.2 / c.1) * g t := fun t => by
      have := hfg t
      field_simp
      linear_combination this
    rw [hf x, hf y]
    ring

/--
[Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.lean)
-/
@[path]
private lemma main
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {X : ι → Type}
  {Φ : (∀ i, X i) → ℂ}
  {i₀ : ι}
  {b₀ t : ∀ j, X j}
  -- given
  (h : ∀ i, i ≠ i₀ → ∀ b b' : ∀ j, X j, ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t : X i, c.1 * Φ (Function.update b i t) + c.2 * Φ (Function.update b' i t) = 0) :
  -- imply
  Φ t * Φ b₀ ^ (Fintype.card ι - 1) = Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ Finset.univ.erase i₀, Φ (Function.update b₀ i (t i)) := by
  -- proof
  classical
  have step : ∀ S : Finset ι, i₀ ∉ S → ∀ t : ∀ j, X j, (∀ j, j ∉ S → j ≠ i₀ → t j = b₀ j) → Φ t * Φ b₀ ^ S.card = Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ S, Φ (Function.update b₀ i (t i)) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    ·
      intro _ t ht
      have hteq : t = Function.update b₀ i₀ (t i₀) := by
        funext j
        if hj : j = i₀ then
          subst hj
          simp
        else
          rw [Function.update_of_ne hj]
          apply ht j (by simp) hj
      simp only [Finset.card_empty, pow_zero, mul_one, Finset.prod_empty]
      rw [← hteq]
    ·
      intro i S hiS ih
      intro hi₀ t ht
      have hii₀ : i ≠ i₀ := fun h => hi₀ (h ▸ Finset.mem_insert_self i S)
      have hi₀S : i₀ ∉ S := fun h => hi₀ (Finset.mem_insert_of_mem h)
      set t' : ∀ j, X j := Function.update t i (b₀ i) with ht'
      have ht'agree : ∀ j, j ∉ S → j ≠ i₀ → t' j = b₀ j := by
        intro j hjS hji₀
        if hji : j = i then
          subst hji
          simp [ht']
        else
          rw [ht', Function.update_of_ne hji]
          apply ht j (by simp [hji, hjS]) hji₀
      have hIH := ih hi₀S t' ht'agree
      have hex : Φ t * Φ b₀ = Φ t' * Φ (Function.update b₀ i (t i)) := by
        have hd := det_eq_of_dep (x := t i) (y := b₀ i) (h i hii₀ t b₀)
        simp only [Function.update_eq_self] at hd
        rw [ht']
        apply hd
      have ht'i₀ : t' i₀ = t i₀ := by
        rw [ht', Function.update_of_ne (Ne.symm hii₀)]
      have ht'S : ∀ j ∈ S, Function.update b₀ j (t' j) = Function.update b₀ j (t j) := by
        intro j hj
        have hji : j ≠ i := fun h => hiS (h ▸ hj)
        rw [ht', Function.update_of_ne hji]
      rw [Finset.card_insert_of_notMem hiS, pow_succ, ← mul_assoc, mul_comm (Φ t), mul_assoc, hex, Finset.prod_insert hiS]
      calc
        _ = (Φ t' * Φ b₀ ^ S.card) * Φ (Function.update b₀ i (t i)) := by
          ring
        _ = (Φ (Function.update b₀ i₀ (t' i₀)) * ∏ j ∈ S, Φ (Function.update b₀ j (t' j))) * Φ (Function.update b₀ i (t i)) := by
          rw [hIH]
        _ = Φ (Function.update b₀ i₀ (t i₀)) * (Φ (Function.update b₀ i (t i)) * ∏ j ∈ S, Φ (Function.update b₀ j (t j))) := by
          rw [ht'i₀, Finset.prod_congr rfl (fun j hj => by rw [ht'S j hj])]
          ring
  have hS := step (Finset.univ.erase i₀) (Finset.notMem_erase i₀ _) t (fun j hj hji₀ => absurd (Finset.mem_erase.2 ⟨hji₀, Finset.mem_univ j⟩) hj)
  rwa [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ] at hS


-- created on 2026-10-20
