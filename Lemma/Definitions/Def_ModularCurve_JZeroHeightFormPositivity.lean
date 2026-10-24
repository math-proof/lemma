import Lemma.Definitions.Def_ModularCurve_JZeroHeightForm
import Lemma.Definitions.Def_Compat_Mathlib430
set_option autoImplicit false
set_option Elab.async false

open ModularCurve AlgebraicCurve

namespace ModularCurve.JZero

noncomputable def offBaseMass (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℤ :=
  (D.erase (cuspInftyBar N)).sum fun _ m => m

noncomputable def baseMass (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  (D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * baseHt s (cuspInftyBar N) v

noncomputable def heightPairing (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  baseHt s (cuspInftyBar N) v + baseHt s (cuspInftyBar N) w - pairHt s v w

theorem baseHt_eq_pointHt (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : v ≠ cuspInftyBar N)
    (hchord : absLogHeight (chordVec s v (cuspInftyBar N)) = 0)
    (hbase : pointHt s (cuspInftyBar N) = 0) :
    baseHt s (cuspInftyBar N) v = pointHt s v := by
  simp [baseHt, pairHt, hv, hchord, hbase]

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

theorem divNaiveHeight_zero_left (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    divNaiveHeight N K 0 D = 0 := by
  haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
  unfold divNaiveHeight
  split_ifs with h
  · exact Height.logHeight_eq_zero_of_subsingleton _
  · rfl

theorem divNaiveHeight_zero_left_le (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (x : ℝ) :
    divNaiveHeight N K 0 D ≤ 0 * x + 0 := by
  rw [divNaiveHeight_zero_left, zero_mul, add_zero]

theorem heightFormPositivityData_of_not_isEmbBasis (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (μ : ℝ)
    (hs : ¬ IsEmbBasis N s) : HeightFormPositivityData N K g' s μ where
  naiveHeight_le_baseMass := fun h => absurd h hs
  pairInteraction := fun h => absurd h hs
  multiPoint := fun h => absurd h hs

theorem heightFormPositivityData_zero (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) :
    HeightFormPositivityData N K 0 s 0 where
  naiveHeight_le_baseMass := fun _ =>
    ⟨0, 0, le_rfl, fun _ D _ => divNaiveHeight_zero_left_le N K D _⟩
  pairInteraction := fun _ hμ => absurd hμ (lt_irrefl 0)
  multiPoint := fun _ hμ => absurd hμ (lt_irrefl 0)

end ModularCurve.JZero
