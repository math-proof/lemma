import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.SLE.CapacityProps
open Filter Topology Complex Bornology StatMech StatMech.SLE


/--
[tendsto_cocompact_iff_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma tendsto_cocompact_iff_norm_eq
  {l : Filter ℂ}
  {f : ℂ → ℂ} :
-- imply
  Tendsto f l (cocompact ℂ) ↔ Tendsto (fun z => ‖f z‖) l atTop := by
-- proof
  apply StatMech.SLE.tendsto_cocompact_iff_norm l f

/--
[eventually_ne_zero_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma eventually_ne_zero_cocompact_eq :
-- imply
  ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 := by
-- proof
  apply StatMech.SLE.eventually_ne_zero_cocompact

/--
[tendsto_inv_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma tendsto_inv_cocompact_eq :
-- imply
  Tendsto (fun z : ℂ => z⁻¹) (cocompact ℂ) (nhds 0) := by
-- proof
  apply StatMech.SLE.tendsto_inv_cocompact

/--
[tendsto_div_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma tendsto_div_cocompact_eq
  {r : ℂ}
-- given
  (hr : r ≠ 0) :
-- imply
  Tendsto (fun z : ℂ => z / r) (cocompact ℂ) (cocompact ℂ) := by
-- proof
  apply StatMech.SLE.tendsto_div_cocompact hr

/--
[tendsto_translate_cocompact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma tendsto_translate_cocompact_eq
  {c : ℂ} :
-- imply
  Tendsto (fun z : ℂ => z + c) (cocompact ℂ) (cocompact ℂ) := by
-- proof
  apply StatMech.SLE.tendsto_translate_cocompact c

/--
[tendsto_cocompact_of_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma tendsto_cocompact_of_sub_eq
  {g : ℂ → ℂ}
-- given
  (h0 : Tendsto (fun z => g z - z) (cocompact ℂ) (nhds 0)) :
-- imply
  Tendsto g (cocompact ℂ) (cocompact ℂ) := by
-- proof
  apply StatMech.SLE.tendsto_cocompact_of_sub h0

/--
[tendsto_div_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma tendsto_div_self_eq
  {g : ℂ → ℂ}
-- given
  (h0 : Tendsto (fun z => g z - z) (cocompact ℂ) (nhds 0)) :
-- imply
  Tendsto (fun z => z / g z) (cocompact ℂ) (nhds 1) := by
-- proof
  apply StatMech.SLE.tendsto_div_self h0

/--
[hasHalfPlaneCapacity_neg_example](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_neg_example_eq :
-- imply
  HasHalfPlaneCapacity (fun z => z - z⁻¹) (-1) := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_neg_example

/--
[HasHalfPlaneCapacity.comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma comp_eq
  {g₁ g₂ : ℂ → ℂ}
  {a₁ a₂ : ℝ}
-- given
  (h₁ : HasHalfPlaneCapacity g₁ a₁)
  (h₂ : HasHalfPlaneCapacity g₂ a₂) :
-- imply
  HasHalfPlaneCapacity (g₂ ∘ g₁) (a₁ + a₂) := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.comp h₁ h₂

/--
[HasHalfPlaneCapacity.le_of_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma le_of_comp_eq
  {g h g' : ℂ → ℂ}
  {a b a' : ℝ}
-- given
  (hg : HasHalfPlaneCapacity g a)
  (hh : HasHalfPlaneCapacity h b)
  (hb : 0 ≤ b)
  (hfac : g' = h ∘ g)
  (hg' : HasHalfPlaneCapacity g' a') :
-- imply
  a ≤ a' := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.le_of_comp hg hh hb hfac hg'

/--
[HasHalfPlaneCapacity.scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma scale_eq
  {g : ℂ → ℂ}
  {a : ℝ}
  {r : ℝ}
-- given
  (hr : r ≠ 0)
  (hg : HasHalfPlaneCapacity g a) :
-- imply
  HasHalfPlaneCapacity (fun z => (r : ℂ) * g (z / r)) (r ^ 2 * a) := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.scale hr hg

/--
[HasHalfPlaneCapacity.translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma translate_eq
  {g : ℂ → ℂ}
  {a : ℝ}
  {c : ℂ}
-- given
  (hg : HasHalfPlaneCapacity g a) :
-- imply
  HasHalfPlaneCapacity (fun z => g (z - c) + c) a := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.translate c hg

/--
[hasHalfPlaneCapacity_halfDisk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_halfDisk_eq
  {c : ℝ} :
-- imply
  HasHalfPlaneCapacity (fun z => z + (c : ℂ) / z) c := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_halfDisk c

/--
[halfDisk_capacity_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma halfDisk_capacity_eq_eq
  {c a : ℝ}
-- given
  (h : HasHalfPlaneCapacity (fun z => z + (c : ℂ) / z) a) :
-- imply
  a = c := by
-- proof
  apply StatMech.SLE.halfDisk_capacity_eq h

/--
[halfDisk_scale_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma halfDisk_scale_consistent_eq
  {r : ℝ}
-- given
  (hr : r ≠ 0) :
-- imply
  HasHalfPlaneCapacity (fun z => (r : ℂ) * ((z / r) + (1 : ℂ) / (z / r))) (r ^ 2 * 1) := by
-- proof
  apply StatMech.SLE.halfDisk_scale_consistent hr

/--
[halfDisk_scale_eq_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma halfDisk_scale_eq_formula_eq
  {r : ℝ}
  {z : ℂ}
-- given
  (hr : r ≠ 0)
  (hz : z ≠ 0) :
-- imply
  (r : ℂ) * ((z / r) + (1 : ℂ) / (z / r)) = z + ((r ^ 2 : ℝ) : ℂ) / z := by
-- proof
  apply StatMech.SLE.halfDisk_scale_eq_formula hr hz

/--
[hasHalfPlaneCapacity_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma hasHalfPlaneCapacity_empty_eq :
-- imply
  HasHalfPlaneCapacity id 0 := by
-- proof
  apply StatMech.SLE.hasHalfPlaneCapacity_empty

/--
[HasHalfPlaneCapacity.comp_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma comp_id_eq
  {g : ℂ → ℂ}
  {a : ℝ}
-- given
  (hg : HasHalfPlaneCapacity g a) :
-- imply
  HasHalfPlaneCapacity (g ∘ id) (0 + a) := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.comp_id hg

/--
[HasHalfPlaneCapacity.id_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/CapacityProps.lean)
-/
@[path]
private lemma id_comp_eq
  {g : ℂ → ℂ}
  {a : ℝ}
-- given
  (hg : HasHalfPlaneCapacity g a) :
-- imply
  HasHalfPlaneCapacity (id ∘ g) (a + 0) := by
-- proof
  apply StatMech.SLE.HasHalfPlaneCapacity.id_comp hg


-- created on 2026-10-23
