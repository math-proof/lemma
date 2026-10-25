/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PuiseuxTheorem.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.HahnSeries.Valuation
import Mathlib.RingTheory.Valuation.ValuationSubring
import Lemma.Polynomial.HenselFactorization
import Def.FieldTheory.PuiseuxTheorem.Part8
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

noncomputable section

open Polynomial

namespace puiseux

theorem exists_root_monic_of_natDegree_le {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] (n : ℕ) :
    ∀ f : (HahnSeries Rat K)[X], f.Monic → 0 < f.natDegree →
      f.natDegree ≤ n → ∃ x, f.IsRoot x := by
  let _ : CharZero (HahnSeries Rat K) :=
    charZero_of_injective_ringHom
      (show Function.Injective (HahnSeries.C : K →+* HahnSeries Rat K) from
        HahnSeries.C_injective)
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro f hf hn hfn
      let d := depressed f
      have hdmonic : d.Monic := depressed_monic f hf
      have hddeg : d.natDegree = f.natDegree := depressed_natDegree f
      have hdn : 0 < d.natDegree := hddeg.symm ▸ hn
      have hdnext : d.nextCoeff = 0 := depressed_nextCoeff f hf hn
      by_cases hdpow : d = X ^ d.natDegree
      · have hdroot : d.IsRoot 0 := by
          rw [hdpow, Polynomial.IsRoot, Polynomial.eval_pow, Polynomial.eval_X]
          exact zero_pow hdn.ne'
        exact ⟨center f, by simpa using root_of_root_depressed f hdroot⟩
      · let p := newtonPolynomial d hdmonic hdpow
        let r := puiseux_residuePolynomial p
        have hpmonic : p.Monic := newtonPolynomial_monic d hdmonic hdpow
        have hrmonic : r.Monic := residuePolynomial_monic d hdmonic hdpow
        have hrdeg : r.natDegree = d.natDegree :=
          residuePolynomial_natDegree d hdmonic hdpow
        have hrnext : r.nextCoeff = 0 :=
          residuePolynomial_nextCoeff_eq_zero d hdmonic hdn hdnext hdpow
        have hrpow : r ≠ X ^ d.natDegree :=
          residuePolynomial_ne_X_pow d hdmonic hdpow
        obtain ⟨g, q, hg, hq, hrfac, hcop, hgpos, hglt, _, _⟩ :=
          split_residue r d.natDegree hrmonic hdn hrdeg hrnext hrpow
        obtain ⟨G, Q, hG, hQ, hpGQ, hGdeg, _⟩ :=
          puiseux_lift_factorization p hpmonic g q hg hq hrfac hcop
        let σ := ValuationSubring.subtype (O K)
        let GF : (HahnSeries Rat K)[X] := G.map σ
        let QF : (HahnSeries Rat K)[X] := Q.map σ
        have hGFmonic : GF.Monic := hG.map σ
        have hGFdeg : GF.natDegree = g.natDegree := by
          exact hG.natDegree_map σ |>.trans hGdeg
        have hGFpos : 0 < GF.natDegree := hGFdeg.symm ▸ hgpos
        have hGFlt : GF.natDegree < n := by
          rw [hGFdeg]
          exact hglt.trans_le (hddeg.trans_le hfn)
        obtain ⟨x, hx⟩ := ih GF.natDegree hGFlt GF hGFmonic hGFpos le_rfl
        have hpmap : p.map σ = GF * QF := by
          rw [hpGQ, Polynomial.map_mul]
        have hpx : (p.map σ).IsRoot x := by
          rw [hpmap]
          exact Polynomial.root_mul_right_of_isRoot QF hx
        have hdx := root_of_root_newtonPolynomial d hdmonic hdpow hpx
        exact
          ⟨HahnSeries.single (newtonSlope d hdmonic hdpow) 1 * x + center f,
            root_of_root_depressed f hdx⟩

theorem exists_root_monic {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] (f : (HahnSeries Rat K)[X])
    (hf : f.Monic) (hn : 0 < f.natDegree) : ∃ x, f.IsRoot x :=
  exists_root_monic_of_natDegree_le (K := K) f.natDegree f hf hn le_rfl

theorem hahnSeries_isAlgClosed {K : Type*} [Field K]
    [IsAlgClosed K] [CharZero K] : IsAlgClosed (HahnSeries Rat K) := by
  apply IsAlgClosed.of_exists_root
  intro f hf hirr
  exact exists_root_monic f hf
    (natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hirr))

end puiseux
end
end MetaMathlibExt
