import Lemma.ModularCurve.JZeroHeightForm
import Instance.Compat_Mathlib430
import Def.ModularCurve_JZeroHeightFormPositivity
set_option autoImplicit false
set_option Elab.async false

open ModularCurve AlgebraicCurve

namespace ModularCurve.JZero


structure HeightFormPositivityData (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (μ : ℝ) : Prop where

  naiveHeight_le_baseMass :
    IsEmbBasis N s →
    ∃ κ C : ℝ, 0 ≤ κ ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        divNaiveHeight N K g' D ≤ κ * baseMass N s D + C

  pairInteraction :
    IsEmbBasis N s →
    0 < μ →
    (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) < μ ^ 2 →
    ∃ C ηE CE : ℝ, 0 < ηE ∧
      ∃ Ex : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ×
                  Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ v w, v ≠ w → v ≠ cuspInftyBar N → w ≠ cuspInftyBar N → (v, w) ∉ Ex →
          -μ * (baseHt s (cuspInftyBar N) v + baseHt s (cuspInftyBar N) w) - C
            ≤ heightPairing N s v w) ∧
        (∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
           (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
           IsRepOf N K g' c D →
           (∃ v w, v ≠ w ∧ v ≠ cuspInftyBar N ∧ w ≠ cuspInftyBar N ∧
             D v ≠ 0 ∧ D w ≠ 0 ∧ (v, w) ∈ Ex) →
           ∃ D₀, IsRepOf N K g' c D₀ ∧
             ηE * divNaiveHeight N K g' D₀ - CE ≤ heightForm N s D₀)

  multiPoint :
    IsEmbBasis N s →
    0 < μ →
    ∃ η C : ℝ, 0 < η ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
          ≤ μ * ((offBaseMass N D : ℝ) - 1) →
        ∃ D₂, IsRepOf N K g' c D₂ ∧
          η * baseMass N s D₂ - C ≤ heightForm N s D₂


end ModularCurve.JZero
