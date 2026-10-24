import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.GHSConcavity
open Finset SimpleGraph Set StatMech StatMech.Sharpness


/--
[shg_concaveOn_antitoneOn_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_concaveOn_antitoneOn_deriv_eq
  {φ : ℝ → ℝ}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) φ)
  (hdiff : ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ φ h) :
-- imply
  AntitoneOn (deriv φ) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.shg_concaveOn_antitoneOn_deriv φ hconc hdiff

/--
[shg_concaveOn_slope_anti](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_concaveOn_slope_anti_eq
  {φ : ℝ → ℝ}
  {x : ℝ}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) φ)
  (hx : x ∈ Ici (0 : ℝ)) :
-- imply
  AntitoneOn (slope φ x) ((Ici 0) \ {x}) := by
-- proof
  apply StatMech.Sharpness.shg_concaveOn_slope_anti φ hconc hx

/--
[shg_concaveOn_deriv_le_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_concaveOn_deriv_le_slope_eq
  {φ : ℝ → ℝ}
  {a b : ℝ}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) φ)
  (ha : a ∈ Ici (0 : ℝ))
  (hb : b ∈ Ici (0 : ℝ))
  (hab : a < b)
  (hd : DifferentiableAt ℝ φ b) :
-- imply
  deriv φ b ≤ (φ b - φ a) / (b - a) := by
-- proof
  apply StatMech.Sharpness.shg_concaveOn_deriv_le_slope φ hconc ha hb hab hd

/--
[shg_concaveOn_slope_anti_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_concaveOn_slope_anti_adjacent_eq
  {φ : ℝ → ℝ}
  {x y z : ℝ}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) φ)
  (hx : x ∈ Ici (0 : ℝ))
  (hz : z ∈ Ici (0 : ℝ))
  (hxy : x < y)
  (hyz : y < z) :
-- imply
  (φ z - φ y) / (z - y) ≤ (φ y - φ x) / (y - x) := by
-- proof
  apply StatMech.Sharpness.shg_concaveOn_slope_anti_adjacent φ hconc hx hz hxy hyz

/--
[shg_concaveOn_of_deriv2_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_concaveOn_of_deriv2_nonpos_eq
  {φ : ℝ → ℝ}
-- given
  (hcont : ContinuousOn φ (Ici 0))
  (hf' : DifferentiableOn ℝ φ (interior (Ici 0)))
  (hf'' : DifferentiableOn ℝ (deriv φ) (interior (Ici 0)))
  (hu3 : ∀ h ∈ interior (Ici (0 : ℝ)), deriv^[2] φ h ≤ 0) :
-- imply
  ConcaveOn ℝ (Ici 0) φ := by
-- proof
  apply StatMech.Sharpness.shg_concaveOn_of_deriv2_nonpos φ hcont hf' hf'' hu3

/--
[shg_magnetization_differentiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_magnetization_differentiable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V} :
-- imply
  ∀ h ∈ Ici (0 : ℝ), DifferentiableAt ℝ (fun h => isingExpectation G β h (fun s => spin s o)) h := by
-- proof
  apply StatMech.Sharpness.shg_magnetization_differentiable G β o

/--
[shg_magnetization_antitoneOn_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_magnetization_antitoneOn_deriv_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
-- imply
  AntitoneOn (deriv (fun h => isingExpectation G β h (fun s => spin s o))) (Ici 0) := by
-- proof
  apply StatMech.Sharpness.shg_magnetization_antitoneOn_deriv G β o hconc

/--
[shg_magnetization_deriv_le_slope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_magnetization_deriv_le_slope_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
  {a b : ℝ}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)))
  (ha : a ∈ Ici (0 : ℝ))
  (hb : b ∈ Ici (0 : ℝ))
  (hab : a < b) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) b ≤ (isingExpectation G β b (fun s => spin s o) - isingExpectation G β a (fun s => spin s o)) / (b - a) := by
-- proof
  apply StatMech.Sharpness.shg_magnetization_deriv_le_slope G β o hconc ha hb hab

/--
[shg_magnetization_slope_anti](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_magnetization_slope_anti_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {o : V}
  {x : ℝ}
-- given
  (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)))
  (hx : x ∈ Ici (0 : ℝ)) :
-- imply
  AntitoneOn (slope (fun h => isingExpectation G β h (fun s => spin s o)) x) ((Ici 0) \ {x}) := by
-- proof
  apply StatMech.Sharpness.shg_magnetization_slope_anti G β o hconc hx

/--
[shg_magnetization_susceptibility_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/GHSConcavity.lean)
-/
@[path]
private lemma shg_magnetization_susceptibility_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o : V}
-- given
  (β h : ℝ)
  (hh : 0 < h)
  (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
-- imply
  deriv (fun h => isingExpectation G β h (fun s => spin s o)) h ≤ isingExpectation G β h (fun s => spin s o) / h := by
-- proof
  apply StatMech.Sharpness.shg_magnetization_susceptibility_bound G β h hh o hconc


-- created on 2026-10-23
