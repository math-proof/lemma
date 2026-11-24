import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Arrow.booleanFourier.influence_zero_invariant
open BooleanFourier Bool


/--
[arrow_impossibility](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Arrow.lean)
-/
@[path]
private lemma main
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hm : m ≥ 3)
  (hunanimous : IsUnanimous f)
  (hodd : IsOdd f)
  (hviable : IsArrowViable f m) :
-- imply
  IsDictator f := by
-- proof
  classical
  have htt := hunanimous.1
  have hff := hunanimous.2
  have hexists_inf : ∃ i : Fin n, influence f i > 0 := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hzero : ∀ i : Fin n, influence f i = 0 := by
      intro i
      apply le_antisymm (h i)
      unfold influence
      exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
    have hinv : ∀ i : Fin n, ∀ x : Fin n → Bool, f x = f (flipCoord x i) :=
      fun i => influence_zero_invariant (hzero i)
    suffices hconst : ∀ (x y : Fin n → Bool), f x = f y by
      have := hconst (fun _ => true) (fun _ => false)
      rw [htt, hff] at this; exact Bool.noConfusion this
    intro x y
    suffices hsuff : ∀ (S : Finset (Fin n)),
      ∀ (z : Fin n → Bool), (∀ k, k ∉ S → z k = y k) → f z = f y by
      exact hsuff Finset.univ x (fun k hk => absurd (Finset.mem_univ k) hk)
    intro S
    refine Finset.induction_on (s := S) ?_ ?_
    ·
      intro z hz
      congr 1
      funext k
      exact hz k (Finset.notMem_empty k)
    ·
      intro a_elem a_set _ a_ih z hz
      if hza : z a_elem = y a_elem then
        apply a_ih z
        intro k hk
        if hka : k = a_elem then
          simpa only [hka] using hza
        else
          exact hz k (by simp [Finset.mem_insert, hka, hk])
      else
        rw [hinv a_elem z]
        apply a_ih (flipCoord z a_elem)
        intro k hk
        if hka : k = a_elem then
          simpa only [hka] using flipCoord_eq_of_ne hza
        else
          simp only [flipCoord, Function.update, dite_eq_right hka]
          exact hz k (by simp [Finset.mem_insert, hka, hk])
  obtain ⟨i₀, hi₀⟩ := hexists_inf
  have hunique : ∀ j : Fin n, j ≠ i₀ → influence f j = 0 := by
    intro j hj
    by_contra hjne
    apply hj
    symm
    apply arrow_viable_implies_unique_pivot (f := f) (i := i₀) (j := j) hm hviable hodd hi₀
    apply lt_of_le_of_ne _ (Ne.symm hjne)
    unfold influence
    exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n)
  have hinv_others : ∀ j : Fin n, j ≠ i₀ → ∀ x : Fin n → Bool, f x = f (flipCoord x j) :=
    fun j hj => influence_zero_invariant (hunique j hj)
  refine ⟨i₀, fun x => ?_⟩
  suffices hdep : f x = f (fun _ => x i₀) by
    rw [hdep]; cases hxi : x i₀ <;> simp [htt, hff]
  suffices hsuff : ∀ (S : Finset (Fin n)),
    (∀ k ∈ S, k ≠ i₀) →
    ∀ (z : Fin n → Bool), z i₀ = x i₀ → (∀ k, k ∉ S → z k = x i₀) →
    f z = f (fun _ => x i₀) by
    apply hsuff (Finset.univ.filter (fun k => k ≠ i₀))
    ·
      intro k hk
      exact (Finset.mem_filter.mp hk).2
    · exact rfl
    ·
      intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and, Classical.not_not] at hk
      subst hk
      rfl
  intro S
  refine Finset.induction_on (s := S) ?_ ?_
  ·
    intro _ z _ hz
    congr 1
    funext k
    exact hz k (Finset.notMem_empty k)
  ·
    intro a_elem a_set _ a_ih hne z hzi hz
    have hane : a_elem ≠ i₀ := hne a_elem (Finset.mem_insert_self a_elem a_set)
    have hne' : ∀ k ∈ a_set, k ≠ i₀ := fun k hk => hne k (Finset.mem_insert_of_mem hk)
    if hza : z a_elem = x i₀ then
      apply a_ih hne' z hzi
      intro k hk
      if hka : k = a_elem then
        simpa only [hka] using hza
      else
        exact hz k (by simp [Finset.mem_insert, hka, hk])
    else
      rw [hinv_others a_elem hane z]
      apply a_ih hne' (flipCoord z a_elem)
        (by simp only [flipCoord, Function.update, dite_eq_right (Ne.symm hane)]; exact hzi)
      intro k hk
      if hka : k = a_elem then
        simpa only [hka] using flipCoord_eq_of_ne hza
      else
        simp only [flipCoord, Function.update, dite_eq_right hka]
        exact hz k (by simp [Finset.mem_insert, hka, hk])


lemma BooleanFourier.arrow_impossibility
  {n m : ℕ}
  {f : (Fin n → Bool) → Bool}
-- given
  (hm : m ≥ 3)
  (hunanimous : IsUnanimous f)
  (hodd : IsOdd f)
  (hviable : IsArrowViable f m) :
-- imply
  IsDictator f :=
-- proof
  main hm hunanimous hodd hviable


-- created on 2026-10-23
-- updated on 2026-11-24
