import Mathlib
import Abbrev.Analysis.Misc.erdos_379
open Nat

/-! Formalizing a proof of Erdos problem \#379, arising from conversations between Stijn Cambie, Vjeko Kovac, and Terry Tao.  See the discussion at https://www.erdosproblems.com/forum/thread/379 -/


/-- The condition {lean}`1<n` is necessary to avoid the range of {lit}`k` being vacuous. -/
theorem S_ge {n r:ℕ} (hn: 1 < n) (h: ∀ k ∈ Finset.Ico 1 n, ∃ p, p.Prime ∧ p^r ∣ n.choose k) : r ≤ S n := by
  apply le_csSup
  . rw [bddAbove_def]; use n; simp; intro r h
    have ⟨ p, hp, hp' ⟩ := h 1 ?_ hn; simp at hp'; apply le_of_dvd at hp'
    have := r.lt_pow_self hp.one_lt
    all_goals grind
  aesop

/-- If $$p>2^\{r-1\}$$, then $$S(2^\{\phi(p^R)\}) \ge r$$. -/
theorem key_cor {p r:ℕ} (hp: p.Prime) (hpr: p > 2^(r-1)) (hr: 1 < r) :
  r ≤ S (2^((p^r).totient)) := by
  apply S_ge; simp; grind
  intro k hk; simp at hk
  have := key_prop rfl hk.1 hk.2 hp hpr hr ?_; swap
  . have := hp.one_lt
    have := (r-1).lt_pow_self this
    have : p^(r-1) ≤ (p^r).totient := by
      rw [totient_prime_pow hp]; apply Nat.le_mul_of_pos_right; omega; omega
    omega
  rcases this with _ | _
  . use 2; simp_all [prime_two]
  use p

/-- A positive resolution to Erdos problem \#379. -/
theorem erdos_379 : Filter.atTop.limsup (fun n ↦ (S n:ENat)) = ⊤ := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  simp; intro N; rw [iSup₂_eq_top]; intro r hr; lift r to ℕ using (by order)
  have ⟨ p, hp, hp' ⟩ := exists_infinite_primes (max N (2^(r+1)+1))
  use 2^((p^(r+2)).totient), ?_
  . have := key_cor hp' (r := r+2) ?_ ?_ <;> simp at * <;> grind
  trans p; order
  have := hp'.one_lt
  have := (p-1).lt_two_pow_self
  have : 2^(p-1) ≤ 2 ^ (p ^ (r + 2)).totient := by
    rw [totient_prime_pow hp']
    gcongr
    · have hmul : p - 1 ≤ p ^ (r + 1) * (p - 1) :=
        Nat.le_mul_of_pos_left (p - 1) (by positivity)
      have h1 : 1 ≤ p := hp'.one_lt.le
      simpa [Nat.sub_add_cancel h1] using Nat.add_le_add_right hmul 1
    omega
  grind

