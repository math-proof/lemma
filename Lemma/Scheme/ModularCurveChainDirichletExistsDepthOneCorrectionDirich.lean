import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def chainRec (r : ℕ → ℤ) (t : ℤ) : ℕ → ℤ := fun d => (Nat.rec (motive := fun _ => ℤ × ℤ) (0, t) (fun n p => (p.2, 2 * p.2 - p.1 - r (n + 1))) d).1

private lemma chainRec_zero (r : ℕ → ℤ) (t : ℤ) : chainRec r t 0 = 0 := by simp [chainRec]

private lemma chainRec_one (r : ℕ → ℤ) (t : ℤ) : chainRec r t 1 = t := by simp [chainRec]

private lemma chainRec_succ_succ (r : ℕ → ℤ) (t : ℤ) (d : ℕ) : chainRec r t (d + 2) = 2 * chainRec r t (d + 1) - chainRec r t d - r (d + 1) := by simp [chainRec]

private lemma chainRec_laplace (r : ℕ → ℤ) (t : ℤ) (d : ℕ) (hd : 1 ≤ d) : chainRec r t (d - 1) - 2 * chainRec r t d + chainRec r t (d + 1) = - r d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, show e + 1 + 1 = e + 2 from rfl, chainRec_succ_succ]
  ring

private lemma chainRec_eq (r : ℕ → ℤ) (t : ℤ) (d : ℕ) : chainRec r t d = d * t + chainRec r 0 d := by
  induction d using Nat.twoStepInduction
  ·
    simp [chainRec_zero]
  ·
    simp [chainRec_one]
  ·
    rename_i d ih0 ih1
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    push_cast
    ring

private noncomputable def corr (r : ℕ → ℤ) (ν : ℤ) : ℕ → ℤ := fun d => if d = 1 then r d - ν else r d

private lemma chainRec_corr (r : ℕ → ℤ) (ν : ℤ) (d : ℕ) : chainRec (corr r ν) 0 d = chainRec r 0 d + ((d - 1 : ℕ) : ℤ) * ν := by
  induction d using Nat.twoStepInduction
  ·
    simp [chainRec_zero]
  ·
    simp [chainRec_one]
  ·
    rename_i d ih0 ih1
    rw [chainRec_succ_succ, chainRec_succ_succ, ih0, ih1]
    obtain rfl | hdp := Nat.eq_zero_or_pos d
    ·
      simp [chainRec_zero, chainRec_one, corr]
      ring
    ·
      have hc : corr r ν (d + 1) = r (d + 1) := by
        rw [corr, ite_eq_right (show d + 1 ≠ 1 by omega)]
      rw [hc]
      have h1 : ((d + 1 - 1 : ℕ) : ℤ) = d := by omega
      have h2 : ((d - 1 : ℕ) : ℤ) = d - 1 := by omega
      have h3 : ((d + 2 - 1 : ℕ) : ℤ) = d + 1 := by omega
      rw [h1, h2, h3]
      ring

private lemma chainRec_corr_self_eq_zero (r : ℕ → ℤ) (n : ℕ) (hn : 1 ≤ n) : chainRec (corr r (chainRec r 0 n)) (-(chainRec r 0 n)) n = 0 := by
  rw [chainRec_eq, chainRec_corr]
  have : ((n - 1 : ℕ) : ℤ) = n - 1 := by omega
  rw [this]
  ring

/--
[ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_ChainDirichlet_exists_depthOne_correction_dirichlet.lean)
-/
@[path]
private lemma main
  [Finite ι]
  (n : ι → ℕ) (hn : ∀ i, 1 ≤ n i)
  (r : ι → ℕ → ℤ) :
  -- imply
  ∃ (ν : ι → ℤ) (c : ι → ℕ → ℤ),
    (∀ i, n i = 1 → ν i = 0) ∧ (∀ i, c i 0 = 0) ∧ (∀ i d, n i ≤ d → c i d = 0) ∧
      ∀ i d, 1 ≤ d → d + 1 ≤ n i → c i (d - 1) - 2 * c i d + c i (d + 1) = -(if d = 1 then r i d - ν i else r i d) := by
  -- proof
  classical
  let ν : ι → ℤ := fun i => if n i = 1 then 0 else chainRec (r i) 0 (n i)
  let c : ι → ℕ → ℤ := fun i d => if n i ≤ d then 0 else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d
  refine ⟨ν, c, ?_, ?_, ?_, ?_⟩
  ·
    intro i hi
    show (if n i = 1 then (0 : ℤ) else chainRec (r i) 0 (n i)) = 0
    rw [ite_eq_left hi]
  ·
    intro i
    have : ¬ n i ≤ 0 := by
      have := hn i
      omega
    show (if n i ≤ 0 then (0 : ℤ) else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) 0) = 0
    rw [ite_eq_right this, chainRec_zero]
  ·
    intro i d hd
    show (if n i ≤ d then (0 : ℤ) else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d) = 0
    rw [ite_eq_left hd]
  ·
    intro i d hd1 hd2
    have hni : ¬ n i = 1 := by omega
    have hνi : ν i = chainRec (r i) 0 (n i) := by
      show (if n i = 1 then (0 : ℤ) else chainRec (r i) 0 (n i)) = _
      rw [ite_eq_right hni]
    have hc : ∀ e, c i e = if n i ≤ e then 0 else chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) e := fun e => rfl
    have hcorr : corr (r i) (ν i) d = (if d = 1 then r i d - ν i else r i d) := rfl
    have key := chainRec_laplace (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) d hd1
    have hend : chainRec (corr (r i) (ν i)) (-(chainRec (r i) 0 (n i))) (n i) = 0 := by
      rw [hνi]
      apply chainRec_corr_self_eq_zero (r i) (n i) (hn i)
    rw [hc (d - 1), hc d, hc (d + 1), ite_eq_right (show ¬ n i ≤ d - 1 by omega), ite_eq_right (show ¬ n i ≤ d by omega), ← hcorr]
    if h2 : n i ≤ d + 1 then
      have heq : d + 1 = n i := by omega
      rw [ite_eq_left h2, ← key, heq, hend]
    else
      rw [ite_eq_right h2, ← key]


-- created on 2026-10-20
