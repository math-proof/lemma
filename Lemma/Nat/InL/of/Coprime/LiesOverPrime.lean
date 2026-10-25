import Mathlib
import sympy.Basic
import Def.FLTPrelim_Ramification
import Lemma.Int.P2MUtil
open ValuationSubring


/-- ported from external source -/

private lemma  inv_natCast_notMem_of_liesOverPrime
  {L : Type*}
  [Field L]
  (A : ValuationSubring L)
  [CharZero L] {p : ℕ} (hp : p ≠ 0) (hA : A.LiesOverPrime p) :
  ((p : L))⁻¹ ∉ A := by
  intro h
  have hlt : A.valuation (p : L) < 1 := (A.mem_nonunits_iff).mp hA
  have hle : A.valuation ((p : L))⁻¹ ≤ 1 := (A.valuation_le_one_iff _).mpr h
  have hp0 : (p : L) ≠ 0 := by exact_mod_cast hp
  rw [map_inv₀, inv_le_one₀ ((Valuation.pos_iff _).mpr hp0)] at hle
  exact (not_lt.mpr hle) hlt

private lemma _root_.ValuationSubring.inv_natCast_mem_of_coprime_of_liesOverPrime
  {L : Type*}
  [Field L]
  (A : ValuationSubring L)
  {p : ℕ} (hA : A.LiesOverPrime p) {n : ℕ} (hn : n.Coprime p) :
  ((n : L))⁻¹ ∈ A := by
  have hlt : A.valuation (p : L) < 1 := (A.mem_nonunits_iff).mp hA
  have hbez := Nat.gcd_eq_gcd_ab n p
  rw [Nat.Coprime.gcd_eq_one hn] at hbez
  have hn_le : A.valuation (n : L) ≤ 1 := (A.valuation_le_one_iff _).mpr (natCast_mem A n)
  have hn1 : A.valuation (n : L) = 1 := by
    by_contra hne
    have hnlt : A.valuation (n : L) < 1 := lt_of_le_of_ne hn_le hne
    have h1 : (1 : L) = (n : L) * (n.gcdA p : L) + (p : L) * (n.gcdB p : L) := by
      have := congrArg (Int.cast (R := L)) hbez
      push_cast at this
      exact this
    have ha : A.valuation ((n.gcdA p : L)) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
    have hb : A.valuation ((n.gcdB p : L)) ≤ 1 := (A.valuation_le_one_iff _).mpr (intCast_mem A _)
    have : A.valuation (1 : L) < 1 := by
      rw [h1]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      ·
        rw [map_mul]
        calc A.valuation (n : L) * A.valuation (n.gcdA p : L) ≤ A.valuation (n : L) * 1 :=
              mul_le_mul_right ha _
          _ < 1 := by rwa [mul_one]
      ·
        rw [map_mul]
        calc A.valuation (p : L) * A.valuation (n.gcdB p : L) ≤ A.valuation (p : L) * 1 :=
              mul_le_mul_right hb _
          _ < 1 := by rwa [mul_one]
    rw [map_one] at this
    exact lt_irrefl _ this
  apply (A.valuation_le_one_iff _).mp
  rw [map_inv₀, hn1, inv_one]
p2m_export "ValuationSubring" "inv_natCast_mem_of_coprime_of_liesOverPrime"
@[path]
private lemma main
  [Field L]
  {A : ValuationSubring L}
  {p : ℕ}
  {n : ℕ}
-- given
  (hA : A.LiesOverPrime p)
  (hn : n.Coprime p) :
-- imply
  ((n : L))⁻¹ ∈ A :=
-- proof
  A.inv_natCast_mem_of_coprime_of_liesOverPrime hA hn


-- created on 2026-10-23
