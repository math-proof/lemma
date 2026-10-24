import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Parseval
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[plancherel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Parseval.lean)
-/
@[path]
lemma plancherel
  {n : ℕ}
  {f g : (Fin n → Bool) → ℝ} :
-- imply
  ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S = innerProduct f g := by
-- proof
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  unfold innerProduct fourierCoeff
  set c := (1 : ℝ) / (2 : ℝ) ^ n with hc_def
  have hg_exp : ∀ x : Fin n → Bool,
    g x = ∑ S : Finset (Fin n),
      (c * ∑ y : Fin n → Bool, g y * chi S y) * chi S x := by
    intro x
    exact fourier_expansion g x
  have rhs_calc : c * ∑ x : Fin n → Bool, f x * g x =
    c * ∑ x : Fin n → Bool,
      ∑ S : Finset (Fin n), f x * ((c * ∑ y : Fin n → Bool, g y * chi S y) * chi S x) := by
    congr 1
    exact Finset.sum_congr rfl (fun x _ => by rw [hg_exp x, Finset.mul_sum])
  rw [rhs_calc]
  rw [show ∑ x : Fin n → Bool, ∑ S : Finset (Fin n),
    f x * ((c * ∑ y : Fin n → Bool, g y * chi S y) * chi S x) =
    ∑ S : Finset (Fin n), ∑ x : Fin n → Bool,
      f x * ((c * ∑ y : Fin n → Bool, g y * chi S y) * chi S x) from
    Finset.sum_comm]
  have factor_step : ∀ S : Finset (Fin n),
    ∑ x : Fin n → Bool,
      f x * ((c * ∑ y : Fin n → Bool, g y * chi S y) * chi S x) =
    (c * ∑ y : Fin n → Bool, g y * chi S y) *
      ∑ x : Fin n → Bool, f x * chi S x := by
    intro S
    have hrw : ∀ x : Fin n → Bool,
      f x * ((c * ∑ y : Fin n → Bool, g y * chi S y) * chi S x) =
      (c * ∑ y : Fin n → Bool, g y * chi S y) * (f x * chi S x) := fun x => by ring
    simp_rw [hrw, ← Finset.mul_sum]
  simp_rw [factor_step]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun S _ => by ring)

end BooleanFourier

namespace BooleanFourier

/--
[parseval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Parseval.lean)
-/
@[path]
lemma parseval
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ} :
-- imply
  ∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (f x) ^ 2 := by
-- proof
  have h := plancherel f f
  simp only [innerProduct] at h
  rw [show ∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff f S =
    ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 from
    Finset.sum_congr rfl (fun S _ => by ring)] at h
  rw [h]
  congr 1
  exact Finset.sum_congr rfl (fun x _ => by ring)

end BooleanFourier

namespace BooleanFourier

/--
[claim_2_2](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Parseval.lean)
-/
@[path]
lemma claim_2_2
  {n : ℕ}
  {f g : (Fin n → Bool) → ℝ} :
-- imply
  (∑ S : Finset (Fin n), fourierCoeff f S * fourierCoeff g S = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * g x) ∧ (∑ S : Finset (Fin n), (fourierCoeff f S) ^ 2 = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (f x) ^ 2) :=
-- proof
  ⟨plancherel f g, parseval f⟩

end BooleanFourier


-- created on 2026-10-23
