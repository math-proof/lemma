import sympy.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset


@[main]
private lemma main
  {s : Finset ℕ}
-- given
  (hs : s.Nonempty) :
-- imply
  ∃ c : ℕ → ℤ, s.gcd id = ∑ i ∈ s, i * c i := by
-- proof
  refine Finset.Nonempty.cons_induction (singleton := ?singleton) (cons := ?cons) hs
  case singleton =>
    intro a
    refine ⟨fun i => if i = a then 1 else 0, ?_⟩
    simp
  case cons =>
    intro e s he hs hbase
    obtain ⟨c, hc⟩ := hbase
    set g := s.gcd id with hg
    refine ⟨fun i => if i = e then Nat.gcdB g e else Nat.gcdA g e * c i, ?_⟩
    have hlhs : (Finset.cons e s he).gcd id = Nat.gcd g e := by
      rw [Finset.gcd_cons he, hg]
      simp only [id]
      exact Nat.gcd_comm e g
    rw [hlhs]
    have hcons : (Finset.cons e s he : Finset ℕ) = s ∪ {e} := by
      rw [Finset.cons_eq_insert]
      ext x
      simp
    rw [hcons, Finset.sum_union (h := by simp [he])]
    simp
    rw [Nat.gcd_eq_gcd_ab, hc, Finset.sum_mul]
    have hAC : ∑ x ∈ s, (x : ℤ) * c x * Nat.gcdA g e =
        ∑ x ∈ s, (x : ℤ) * (Nat.gcdA g e * c x) := by
      apply Finset.sum_congr rfl
      intro x hx
      ring
    rw [hAC]
    have hif : ∀ i ∈ s, (if i = e then (↑i : ℤ) * Nat.gcdB g e else (↑i : ℤ) * (Nat.gcdA g e * c i)) =
        (↑i : ℤ) * (Nat.gcdA g e * c i) := by
      intro i hi
      split_ifs with hie
      · exact (he (hie ▸ hi)).elim
      · rfl
    rw [Finset.sum_congr rfl hif]



-- created on 2026-09-18
