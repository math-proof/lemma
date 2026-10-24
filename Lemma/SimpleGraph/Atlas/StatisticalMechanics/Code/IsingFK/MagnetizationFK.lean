import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.IsingFK.MagnetizationFK
open MeasureTheory StatMech StatMech.Ising StatMech.IsingFK


/--
[isSpinMonomial_spin_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean)
-/
@[path]
private lemma isSpinMonomial_spin_glue_eq
  {d : ℕ}
  {n : ℕ}
  {z : Site d} :
-- imply
  IsSpinMonomial (fun τ : {x // x ∈ box d n} → Bool => spin (glue (plusField d) τ) z) := by
-- proof
  apply StatMech.Ising.isSpinMonomial_spin_glue n z

/--
[isSpinMonomial_bond_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean)
-/
@[path]
private lemma isSpinMonomial_bond_glue_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)} :
-- imply
  IsSpinMonomial (fun τ : {x // x ∈ box d n} → Bool => bond (glue (plusField d) τ) e) := by
-- proof
  apply StatMech.Ising.isSpinMonomial_bond_glue n e

/--
[fvWeight_plus_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean)
-/
@[path]
private lemma fvWeight_plus_factor_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  fvWeight (plusField d) n B β 0 τ = ∏ e ∈ B, (Real.cosh β + bond (glue (plusField d) τ) e * Real.sinh β) := by
-- proof
  apply StatMech.Ising.fvWeight_plus_factor n B β τ

/--
[sum_fvWeight_spin_origin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean)
-/
@[path]
private lemma sum_fvWeight_spin_origin_nonneg_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ ∑ τ : {x // x ∈ box d n} → Bool, fvWeight (plusField d) n B β 0 τ * spin (glue (plusField d) τ) (origin d) := by
-- proof
  apply StatMech.Ising.sum_fvWeight_spin_origin_nonneg n B hβ

/--
[fv_integral_origin_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean)
-/
@[path]
private lemma fv_integral_origin_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
  {n : ℕ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ ∫ ω, spin ω (origin d) ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.IsingFK.fv_integral_origin_nonneg d hβ n

/--
[magnetization_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/MagnetizationFK.lean)
-/
@[path]
private lemma magnetization_nonneg_eq
  {d : ℕ}
  {d : ℕ}
  {β : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  0 ≤ Ising.magnetization d β := by
-- proof
  apply StatMech.IsingFK.magnetization_nonneg d hβ


-- created on 2026-10-23
