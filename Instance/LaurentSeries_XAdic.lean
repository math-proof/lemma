-- Carved from Lemma/Definitions/Def_LaurentSeries_XAdic.lean: instance decls only.
import Mathlib

set_option autoImplicit false

noncomputable section

open scoped NNReal
open HahnSeries

namespace LaurentSeries.XAdic

variable (F : Type*) [Field F]

scoped instance rankOne :
    (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankOne := by
  have hv :
      (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ)))
          (HahnSeries.single (1 : ℤ) (1 : F))
        = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by
    simpa [WithZero.exp] using LaurentSeries.valuation_single_zpow (K := F) 1
  haveI hnt : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨⟨HahnSeries.single (1 : ℤ) (1 : F),
      by rw [hv]; exact WithZero.coe_ne_zero,
      by
        rw [hv]
        intro h
        have h' := Multiplicative.ofAdd.injective (WithZero.coe_inj.mp (h.trans rfl : _ =
          ((Multiplicative.ofAdd (0 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))))
        norm_num at h'⟩⟩
  haveI hle : (Valued.v : Valuation (LaurentSeries F) (WithZero (Multiplicative ℤ))).RankLeOne :=
    Valuation.RankLeOne.mk
      ((WithZeroMulInt.toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
        MonoidWithZeroHom.ValueGroup₀.embedding)
      (fun a b hab =>
        WithZeroMulInt.toNNReal_strictMono (by norm_num : (1 : NNReal) < 2)
          (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono hab))
  exact Valuation.RankOne.mk

scoped instance nontriviallyNormedField : NontriviallyNormedField (LaurentSeries F) :=
  Valued.toNontriviallyNormedField (LaurentSeries F) (WithZero (Multiplicative ℤ))

scoped instance isUltrametricDist : IsUltrametricDist (LaurentSeries F) :=
  IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
    (Valued.isNonarchimedean_norm (LaurentSeries F) (WithZero (Multiplicative ℤ)))

scoped instance (priority := low) decidableEq : DecidableEq (LaurentSeries F) := Classical.decEq _

end LaurentSeries.XAdic

end
