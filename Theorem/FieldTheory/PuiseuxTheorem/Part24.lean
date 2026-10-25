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
import Def.FieldTheory.PuiseuxTheorem.Part26
/-!
# Puiseux's theorem

This file proves algebraic closedness of rational-exponent Hahn series and identifies the
bounded-denominator subfield as an algebraic closure of the Laurent series field. It also
records the standard fraction-field equivalence for Laurent and power series.
-/


namespace MetaMathlibExt

namespace MetaMathlibExt

noncomputable section

theorem puiseux_subfield_isAlgebraic {K : Type*} [Field K] :
    let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
    Algebra.IsAlgebraic (LaurentSeries K) ↥(puiseuxSubfield K) := by
  let _ : Algebra (LaurentSeries K) ↥(puiseuxSubfield K) := puiseux_subfieldAlgebra
  constructor
  intro x
  obtain ⟨n, hn, hx⟩ := x.property
  obtain ⟨z, hz⟩ := (puiseux_atLevel_iff hn (x : HahnSeries Rat K)).1 hx
  let y : ↥(puiseuxLevelField K n hn) :=
    ⟨x, by
      rw [puiseuxLevelField, RingHom.mem_fieldRange]
      exact ⟨z, hz⟩⟩
  let _ : Algebra (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_levelAlgebra n hn
  let _ : Module.Finite (LaurentSeries K) ↥(puiseuxLevelField K n hn) :=
    puiseux_level_module_finite hn
  have hy : IsIntegral (LaurentSeries K) y :=
    (IsAlgebraic.of_finite (LaurentSeries K) y).isIntegral
  have hmap := hy.map (puiseux_levelToSubfieldAlgHom hn)
  have heq : puiseux_levelToSubfieldAlgHom hn y = x := by
    apply Subtype.ext
    rfl
  rw [heq] at hmap
  exact hmap.isAlgebraic

/-- Puiseux's theorem (https://en.wikipedia.org/wiki/Puiseux_series):
The set of Puiseux series over an algebraically closed field of characteristic
zero is itself an algebraically closed field (the field of Puiseux series).
Puiseux series are modelled as `HahnSeries Rat K`. The Puiseux field is carried
as the bounded-denominator subfield of `HahnSeries Rat K` (the union over `n`
of `K((t ^ (1 / n)))`, i.e. each series has support denominators dividing some
`n` depending on the series), and it is the algebraic closure of the field of
formal Laurent series, which itself is the field of fractions of the ring of
formal power series.

Proves `Wanted` entry `puiseux_theorem`.

Proof: Newton polygon plus Hensel lifting, first in the rational Hahn field and
then with the ramification bounded inside a power-series level.
-/
theorem puiseux_theorem {K : Type*} [Field K] [IsAlgClosed K]
    [CharZero K] :
    IsAlgClosed (HahnSeries Rat K) ∧
      (∃ (ι : LaurentSeries K →+* HahnSeries Rat K)
          (P : Subfield (HahnSeries Rat K))
          (hmem : ∀ y, ι y ∈ P)
          (e : ↥P ≃+* AlgebraicClosure (LaurentSeries K)),
          Function.Injective ι ∧
            (∀ x : ↥P, ∃ n : ℕ, 0 < n ∧
              ∀ r : Rat, HahnSeries.coeff (x : HahnSeries Rat K) r ≠ 0 →
                ∃ m : ℤ, r = (m : Rat) / (n : Rat)) ∧
            (∀ y : HahnSeries Rat K,
              (∃ n : ℕ, 0 < n ∧
                ∀ r : Rat, HahnSeries.coeff y r ≠ 0 →
                  ∃ m : ℤ, r = (m : Rat) / (n : Rat)) → y ∈ P) ∧
            (∀ y, e ⟨ι y, hmem y⟩ =
              algebraMap (LaurentSeries K)
                (AlgebraicClosure (LaurentSeries K)) y)) ∧
      Nonempty (LaurentSeries K ≃+* FractionRing (PowerSeries K)) := by
  refine ⟨HahnSeries.isAlgClosed_rat, ?_, puiseux_fractionRing_equiv⟩
  let ι : LaurentSeries K →+* HahnSeries Rat K := puiseux_laurentHom
  let P : Subfield (HahnSeries Rat K) := puiseuxSubfield K
  have hmem (y : LaurentSeries K) : ι y ∈ P := puiseux_laurentHom_mem y
  let _ : Algebra (LaurentSeries K) ↥P := puiseux_subfieldAlgebra
  let _ : IsAlgClosed ↥P := puiseux_subfield_isAlgClosed
  let _ : Algebra.IsAlgebraic (LaurentSeries K) ↥P :=
    puiseux_subfield_isAlgebraic
  let _ : IsAlgClosure (LaurentSeries K) ↥P :=
    { isAlgClosed := puiseux_subfield_isAlgClosed
      isAlgebraic := puiseux_subfield_isAlgebraic }
  let ea : ↥P ≃ₐ[LaurentSeries K] AlgebraicClosure (LaurentSeries K) :=
    IsAlgClosure.equiv (LaurentSeries K) ↥P
      (AlgebraicClosure (LaurentSeries K))
  let e : ↥P ≃+* AlgebraicClosure (LaurentSeries K) := ea.toRingEquiv
  refine ⟨ι, P, hmem, e, puiseux_laurentHom_injective, ?_, ?_, ?_⟩
  · intro x
    exact x.property
  · intro y hy
    exact hy
  · intro y
    change ea ⟨ι y, hmem y⟩ =
      algebraMap (LaurentSeries K) (AlgebraicClosure (LaurentSeries K)) y
    exact ea.commutes y

end
end MetaMathlibExt
end MetaMathlibExt
