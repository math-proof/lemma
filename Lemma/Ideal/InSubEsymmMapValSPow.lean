import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma prod_mem_pow
  (A : Type) [CommRing A]
  (I : Ideal A)
  {ι : Type}
  (t : Finset ι)
  (y : ι → A)
  -- given
  (hy : ∀ i ∈ t, y i ∈ I) :
  -- imply
  (∏ i ∈ t, y i) ∈ I ^ t.card := by
  -- proof
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
    apply Ideal.mul_mem_mul (hy a (Finset.mem_insert_self a t))
      (ih fun i hi => hy i (Finset.mem_insert_of_mem hi))

private lemma prod_sub_prod_mem_pow_succ
  (A : Type) [CommRing A]
  (I : Ideal A)
  {ι : Type}
  (t : Finset ι)
  (y z : ι → A)
  -- given
  (hz : ∀ i ∈ t, z i ∈ I)
  (hyz : ∀ i ∈ t, y i - z i ∈ I ^ 2) :
  -- imply
  (∏ i ∈ t, y i) - (∏ i ∈ t, z i) ∈ I ^ (t.card + 1) := by
  -- proof
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    have hy : ∀ i ∈ insert a t, y i ∈ I := by
      intro i hi
      have e : y i = (y i - z i) + z i := by
        ring
      rw [e]
      apply Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (hyz i hi)) (hz i hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have e : y a * ∏ i ∈ t, y i - z a * ∏ i ∈ t, z i = (y a - z a) * ∏ i ∈ t, y i + z a * (∏ i ∈ t, y i - ∏ i ∈ t, z i) := by
      ring
    rw [e, show t.card + 1 + 1 = 2 + t.card by ring]
    refine Ideal.add_mem _ ?_ ?_
    ·
      rw [pow_add]
      apply Ideal.mul_mem_mul (hyz a (Finset.mem_insert_self a t))
        (prod_mem_pow A I t y fun i hi => hy i (Finset.mem_insert_of_mem hi))
    ·
      rw [show 2 + t.card = 1 + (t.card + 1) by ring, pow_add, pow_one]
      apply Ideal.mul_mem_mul (hz a (Finset.mem_insert_self a t))
        (ih (fun i hi => hz i (Finset.mem_insert_of_mem hi)) (fun i hi => hyz i (Finset.mem_insert_of_mem hi)))

/--
[Multiset_esymm_map_sub_esymm_map_mem_pow_succ](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Multiset_esymm_map_sub_esymm_map_mem_pow_succ.lean)
-/
@[path]
private lemma main
  (A : Type) [CommRing A]
  (I : Ideal A)
  (ι : Type)
  (s : Finset ι)
  (y z : ι → A)
  (k : ℕ)
  -- given
  (hz : ∀ i ∈ s, z i ∈ I)
  (hyz : ∀ i ∈ s, y i - z i ∈ I ^ 2) :
  -- imply
  (s.val.map y).esymm k - (s.val.map z).esymm k ∈ I ^ (k + 1) := by
  -- proof
  classical
  rw [Finset.esymm_map_val, Finset.esymm_map_val, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun t ht => ?_
  rw [Finset.mem_powersetCard] at ht
  obtain ⟨hts, htk⟩ := ht
  rw [← htk]
  apply prod_sub_prod_mem_pow_succ A I t y z (fun i hi => hz i (hts hi)) (fun i hi => hyz i (hts hi))


-- created on 2026-10-20
