import Mathlib
import sympy.Basic


/--
[AddSubgroup_exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_exists_forall_mem_iff_single_sub_mul_mem_of_sum_mul_eq_one.lean)
-/

private lemma  single_zero_add_single_one
  {D : Type*}
  [Ring D]
  (a b : D) :
  (Pi.single (0 : Fin 2) a + Pi.single (1 : Fin 2) b : Fin 2 → D) = ![a, b] := by
  funext i
  fin_cases i <;> simp


@[main]
private lemma main
  [Ring D]
  {O : Set D}
  {M : AddSubgroup (Fin 2 → D)}
  {t : Finset ι}
  {x y : ι → D}
-- given
  (hM : ∀ m ∈ M, ∀ o ∈ O, (fun i => m i * o) ∈ M)
  (hx : ∀ k ∈ t, ∃ m ∈ M, m 1 = x k)
  (hy : ∀ k ∈ t, ∀ m ∈ M, y k * m 1 ∈ O)
  (hsum : ∑ k ∈ t, x k * y k = 1) :
-- imply
  ∃ u : D, ∀ v : Fin 2 → D,
      v ∈ M ↔ (Pi.single (0 : Fin 2) (v 0 - u * v 1) ∈ M ∧ ∃ m ∈ M, m 1 = v 1) := by
-- proof
  classical

  let m : ι → (Fin 2 → D) := fun k => if hk : k ∈ t then (hx k hk).choose else 0
  have hm : ∀ k ∈ t, m k ∈ M ∧ m k 1 = x k := by
    intro k hk
    simp only [m, dite_eq_left hk]
    exact (hx k hk).choose_spec
  let u : D := ∑ k ∈ t, m k 0 * y k

  have hsec : ∀ v : Fin 2 → D, (∃ m' ∈ M, m' 1 = v 1) →
      (![u * v 1, v 1] : Fin 2 → D) ∈ M := by
    rintro v ⟨m', hm', hv⟩
    have hmem : (∑ k ∈ t, fun i => m k i * (y k * v 1)) ∈ M := by
      refine AddSubgroup.sum_mem _ fun k hk => ?_
      refine hM _ (hm k hk).1 _ ?_
      rw [← hv]
      exact hy k hk m' hm'
    have heq : (∑ k ∈ t, fun i => m k i * (y k * v 1)) = ![u * v 1, v 1] := by
      funext i
      rw [Finset.sum_apply]
      fin_cases i
      ·
        simp only [u, Fin.zero_eta, Matrix.cons_val_zero, Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by rw [mul_assoc]
      ·
        simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        calc _ = ∑ k ∈ t, x k * y k * v 1 :=
              Finset.sum_congr rfl fun k hk => by rw [(hm k hk).2, mul_assoc]
          _ = v 1 := by rw [← Finset.sum_mul, hsum, one_mul]
    rwa [heq] at hmem
  refine ⟨u, fun v => ⟨fun hv => ?_, fun ⟨h0, h1⟩ => ?_⟩⟩
  ·
    have hs := hsec v ⟨v, hv, rfl⟩
    refine ⟨?_, v, hv, rfl⟩
    have : (Pi.single (0 : Fin 2) (v 0 - u * v 1) : Fin 2 → D) = v - ![u * v 1, v 1] := by
      funext i; fin_cases i <;> simp
    rw [this]
    exact M.sub_mem hv hs
  ·
    have hs := hsec v h1
    have : v = Pi.single (0 : Fin 2) (v 0 - u * v 1) + ![u * v 1, v 1] := by
      funext i; fin_cases i <;> simp
    rw [this]
    exact M.add_mem h0 hs


-- created on 2026-10-09
