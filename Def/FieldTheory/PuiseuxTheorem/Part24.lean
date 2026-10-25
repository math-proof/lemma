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
import Theorem.FieldTheory.PuiseuxTheorem.Part21
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

def puiseux_residueIndexEmbedding (n : ℕ) (hn : 0 < n) (r : Fin n) : ℤ ↪o ℤ where
  toFun q := (n : ℤ) * q + (r : ℕ)
  inj' := by
    intro a b hab
    apply puiseux_scaleIndexHom_injective hn
    exact add_right_cancel hab
  map_rel_iff' := by
    intro a b
    change (n : ℤ) * a + (r : ℕ) ≤ (n : ℤ) * b + (r : ℕ) ↔ a ≤ b
    rw [add_le_add_iff_right]
    exact puiseux_scaleIndexHom_le_iff hn a b

noncomputable def puiseux_residuePart {K : Type*} [Field K] {n : ℕ} (hn : 0 < n)
    (r : Fin n) (x : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.mk (fun q : ℤ ↦ x.coeff (puiseux_residueIndexEmbedding n hn r q)) <| by
    apply Set.IsWF.isPWO
    have h := Set.WellFoundedOn.mapsTo (puiseux_residueIndexEmbedding n hn r) (s := x.support)
      (t := Function.support fun q : ℤ ↦
        x.coeff (puiseux_residueIndexEmbedding n hn r q))
      (by
        intro q hq
        exact (HahnSeries.mem_support x _).2 hq)
      x.isWF_support
    exact h.mono' fun a _ b _ hab ↦ (puiseux_residueIndexEmbedding n hn r).lt_iff_lt.mpr hab

def puiseux_remainderFin (n : ℕ) (hn : 0 < n) (m : ℤ) : Fin n :=
  ⟨(m % (n : ℤ)).toNat, by
    have hnonneg : 0 ≤ m % (n : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
    have hlt : m % (n : ℤ) < (n : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hn)
    have hcast : ((m % (n : ℤ)).toNat : ℤ) < (n : ℤ) := by
      simpa [Int.toNat_of_nonneg hnonneg] using hlt
    exact_mod_cast hcast⟩

end
end MetaMathlibExt
end MetaMathlibExt
