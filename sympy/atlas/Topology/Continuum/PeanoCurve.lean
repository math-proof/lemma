/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Continuum/PeanoCurve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Complex.Tietze
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.MetricSpace.HausdorffAlexandroff

section

/-!
# Peano's space-filling curve
-/

noncomputable section

open Topology

namespace MathlibExt.Topology.Continuum.PeanoCurveWanted

/--
There exists a continuous surjection from the closed unit interval to its square.
Source: G. Peano, "Sur une courbe, qui remplit toute une aire plane",
Mathematische Annalen 36 (1890), 157-160.

Proves `Wanted` entry `peano_curve_exists`.
-/
theorem peano_curve_exists :
    ∃ (f : C(unitInterval, unitInterval × unitInterval)), Function.Surjective f := by
  obtain ⟨g, hg_cont, hg_surj⟩ :=
    exists_nat_bool_continuous_surjective_of_compact (↥unitInterval × ↥unitInterval)
  have h_surj : Function.Surjective (g ∘ cantorSetHomeomorphNatToBool.toFun) :=
    hg_surj.comp cantorSetHomeomorphNatToBool.toEquiv.surjective
  obtain ⟨G, hG⟩ := TietzeExtension.exists_restrict_eq' cantorSet isClosed_cantorSet
    ((⟨g, hg_cont⟩ : C(ℕ → Bool, ↥unitInterval × ↥unitInterval)).comp
      (⟨cantorSetHomeomorphNatToBool.toFun,
        cantorSetHomeomorphNatToBool.continuous_toFun⟩ : C(↥cantorSet, ℕ → Bool)))
  have hGe : ∀ c : ↥cantorSet, G (c.val : ℝ) =
      g (cantorSetHomeomorphNatToBool.toFun c) := fun c =>
    ContinuousMap.congr_fun hG c
  refine ⟨G.comp ⟨Subtype.val, continuous_subtype_val⟩, ?_⟩
  intro y
  obtain ⟨c, hc⟩ := h_surj y
  have hmem : (c.val : ℝ) ∈ unitInterval := cantorSet_subset_unitInterval c.prop
  refine ⟨⟨c.val, hmem⟩, ?_⟩
  rw [← hc]
  exact hGe c

end MathlibExt.Topology.Continuum.PeanoCurveWanted
