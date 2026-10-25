import Lemma.ModularCurve.JZeroHeightForm
import Lemma.Compat.Mathlib430
import Def.ModularCurve_JZeroHeightFormPositivity
import Structure.ModularCurve_JZeroHeightFormPositivity
set_option autoImplicit false
set_option Elab.async false

open ModularCurve AlgebraicCurve

namespace ModularCurve.JZero


theorem baseHt_eq_pointHt (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : v ≠ cuspInftyBar N)
    (hchord : absLogHeight (chordVec s v (cuspInftyBar N)) = 0)
    (hbase : pointHt s (cuspInftyBar N) = 0) :
    baseHt s (cuspInftyBar N) v = pointHt s v := by
  simp [baseHt, pairHt, hv, hchord, hbase]


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
