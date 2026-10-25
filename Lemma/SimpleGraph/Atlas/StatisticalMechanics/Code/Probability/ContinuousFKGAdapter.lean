import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKGAdapter.Part2
open MeasureTheory StatMech StatMech.Probability


/--
[cube_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma cube_eq_eq
  {n : ℕ} :
-- imply
  cube n = Measure.pi (fun _ : Fin n => volume.restrict (Set.Icc (0 : ℝ) 1)) := by
-- proof
  apply StatMech.Probability.cube_eq n

/--
[fkg_of_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma fkg_of_factor_eq
  [MeasurableSpace α]
  [Preorder α]
  {n : ℕ}
  {p : (Fin n → ℝ) → α}
  {f₀ g₀ : α → ℝ}
  {Cf Cg : ℝ}
-- given
  (hpm : Measurable p)
  (hpmono : Monotone p)
  (hf₀m : Measurable f₀)
  (hg₀m : Measurable g₀)
  (hf₀C : ∀ a, |f₀ a| ≤ Cf)
  (hg₀C : ∀ a, |g₀ a| ≤ Cg)
  (hf₀ : Monotone f₀)
  (hg₀ : Monotone g₀) :
-- imply
  (∫ x, f₀ (p x) ∂(cube n)) * (∫ x, g₀ (p x) ∂(cube n)) ≤ ∫ x, f₀ (p x) * g₀ (p x) ∂(cube n) := by
-- proof
  apply StatMech.Probability.fkg_of_factor n p hpm hpmono hf₀m hg₀m hf₀C hg₀C hf₀ hg₀

/--
[restrictCoords_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma restrictCoords_mono_eq
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  Monotone (restrictCoords S) := by
-- proof
  apply StatMech.Probability.restrictCoords_mono S

/--
[measurable_restrictCoords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma measurable_restrictCoords_eq
  {n : ℕ}
  {S : Finset (Fin n)} :
-- imply
  Measurable (restrictCoords S) := by
-- proof
  apply StatMech.Probability.measurable_restrictCoords S

/--
[fkg_of_subset_coords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma fkg_of_subset_coords_eq
  {n : ℕ}
  {S : Finset (Fin n)}
  {f₀ g₀ : ({i // i ∈ S} → ℝ) → ℝ}
  {Cf Cg : ℝ}
-- given
  (hf₀m : Measurable f₀)
  (hg₀m : Measurable g₀)
  (hf₀C : ∀ a, |f₀ a| ≤ Cf)
  (hg₀C : ∀ a, |g₀ a| ≤ Cg)
  (hf₀ : Monotone f₀)
  (hg₀ : Monotone g₀) :
-- imply
  (∫ x, f₀ (restrictCoords S x) ∂(cube n)) * (∫ x, g₀ (restrictCoords S x) ∂(cube n)) ≤ ∫ x, f₀ (restrictCoords S x) * g₀ (restrictCoords S x) ∂(cube n) := by
-- proof
  apply StatMech.Probability.fkg_of_subset_coords S hf₀m hg₀m hf₀C hg₀C hf₀ hg₀

/--
[fkg_second_block_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma fkg_second_block_fiber_eq
  {m n : ℕ}
  {f g : (Fin m → ℝ) × (Fin n → ℝ) → ℝ}
  {Cf Cg : ℝ}
  {U : Fin m → ℝ}
-- given
  (hfm : Measurable f)
  (hgm : Measurable g)
  (hfC : ∀ z, |f z| ≤ Cf)
  (hgC : ∀ z, |g z| ≤ Cg)
  (hf : ∀ U, Monotone (fun V => f (U, V)))
  (hg : ∀ U, Monotone (fun V => g (U, V))) :
-- imply
  (∫ V, f (U, V) ∂(cube n)) * (∫ V, g (U, V) ∂(cube n)) ≤ ∫ V, f (U, V) * g (U, V) ∂(cube n) := by
-- proof
  apply StatMech.Probability.fkg_second_block_fiber hfm hgm hfC hgC hf hg U

/--
[fkg_second_block](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/ContinuousFKGAdapter.lean)
-/
@[path]
private lemma fkg_second_block_eq
  {m n : ℕ}
  {f g : (Fin m → ℝ) × (Fin n → ℝ) → ℝ}
  {Cf Cg : ℝ}
-- given
  (hfm : Measurable f)
  (hgm : Measurable g)
  (hfC : ∀ z, |f z| ≤ Cf)
  (hgC : ∀ z, |g z| ≤ Cg)
  (hf : ∀ U, Monotone (fun V => f (U, V)))
  (hg : ∀ U, Monotone (fun V => g (U, V))) :
-- imply
  (∫ U, (∫ V, f (U, V) ∂(cube n)) * (∫ V, g (U, V) ∂(cube n)) ∂(cube m)) ≤ ∫ z, f z * g z ∂((cube m).prod (cube n)) := by
-- proof
  apply StatMech.Probability.fkg_second_block hfm hgm hfC hgC hf hg


-- created on 2026-10-23
