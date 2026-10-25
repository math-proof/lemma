/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/CollarNeighborhood.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.PartitionOfUnity
import Def.Geometry.Manifold.CollarNeighborhood.Part21
/-!
# Collar neighborhoods of smooth manifold boundaries

This file proves that the boundary of a Hausdorff second-countable smooth manifold modeled on a
Euclidean half-space admits a topological collar neighborhood.
-/


noncomputable section

open Filter Function Manifold Set WithLp

open scoped ContDiff Manifold Topology

namespace MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted

theorem collarFiberTransform_continuous : Continuous collarFiberTransform := by
  apply Continuous.subtype_mk
  let p : collarFiberInput → ℝ := fun z ↦ z.1.1.val
  let q : collarFiberInput → ℝ := fun z ↦ z.1.2.val
  let s : collarFiberInput → ℝ := fun z ↦ z.2.val
  have hp : Continuous p :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have hq : Continuous q :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous s := continuous_subtype_val.comp continuous_snd
  let lower : collarFiberInput → ℝ := fun z ↦
    -2 + (s z + 2) * (2 - q z) / (2 - p z)
  let middle : collarFiberInput → ℝ := fun z ↦
    -q z + (s z + p z) * (q z + 1 / 2) / (p z + 1 / 2)
  have hlower : Continuous lower := by
    exact continuous_const.add (((hs.add continuous_const).mul
      (continuous_const.sub hq)).div (continuous_const.sub hp) fun z ↦
        ne_of_gt (by dsimp [p]; linarith [z.1.1.property.2]))
  have hmiddle : Continuous middle := by
    exact hq.neg.add (((hs.add hp).mul (hq.add continuous_const)).div
      (hp.add continuous_const) fun z ↦
        ne_of_gt (by dsimp [p]; linarith [z.1.1.property.1]))
  change Continuous fun z ↦ if s z ≤ -p z then lower z
    else if s z ≤ (1 / 2 : ℝ) then middle z else s z
  apply Continuous.if_le hlower
    (Continuous.if_le hmiddle hs hs continuous_const ?_) hs hp.neg
  · intro z hz
    have hhalf : s z ≤ (1 / 2 : ℝ) := by
      dsimp [s, p] at hz ⊢
      linarith [z.1.1.property.1]
    rw [ite_eq_left hhalf]
    dsimp [lower, middle, p, q, s] at hz ⊢
    have hden₁ : 2 - z.1.1.val ≠ 0 := ne_of_gt (collarFiberDenomTwoPos z.1.1)
    have hden₂ : z.1.1.val + 1 / 2 ≠ 0 :=
      ne_of_gt (collarFiberDenomHalfPos z.1.1)
    rw [hz]
    field_simp [hden₁, hden₂]
    ring
  · intro z hz
    dsimp [middle, p, q, s]
    dsimp [s] at hz
    have hden : z.1.1.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos z.1.1)
    rw [hz]
    rw [show (1 / 2 : ℝ) + z.1.1.val = z.1.1.val + 1 / 2 by ring]
    rw [mul_div_cancel_left₀ _ hden]
    ring

theorem collarFiberMap_anchor (p q : Set.Icc (0 : ℝ) 1) :
    collarFiberMap p.val q.val (-p.val) = -q.val := by
  rw [collarFiberMap_lower le_rfl]
  have hp : 2 - p.val ≠ 0 := ne_of_gt (collarFiberDenomTwoPos p)
  rw [show -p.val + 2 = 2 - p.val by ring, mul_div_cancel_left₀ _ hp]
  ring

theorem collarFiberMap_self (p : Set.Icc (0 : ℝ) 1)
    (s : Set.Ico (-2 : ℝ) 1) : collarFiberMap p.val p.val s.val = s.val := by
  by_cases hsp : s.val ≤ -p.val
  · rw [collarFiberMap_lower hsp]
    have hp : 2 - p.val ≠ 0 := ne_of_gt (collarFiberDenomTwoPos p)
    rw [mul_div_cancel_right₀ _ hp]
    ring
  · by_cases hs : s.val ≤ (1 / 2 : ℝ)
    · rw [collarFiberMap_middle hsp hs]
      have hp : p.val + 1 / 2 ≠ 0 := ne_of_gt (collarFiberDenomHalfPos p)
      rw [mul_div_cancel_right₀ _ hp]
      ring
    · rw [collarFiberMap_upper p hs]

end MathlibExt.Geometry.Manifold.CollarNeighborhoodWanted
end
