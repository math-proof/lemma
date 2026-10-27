import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Topology.Continuum.PeanoCurve
open Topology
open MathlibExt.Topology.Continuum.PeanoCurveWanted


namespace MathlibExt.Topology.Continuum.PeanoCurveWanted

/--
[peano_curve_exists](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/Continuum/PeanoCurve.lean)
-/
@[path]
lemma peano_curve_exists
  :
-- imply
  ∃ (f : C(unitInterval, unitInterval × unitInterval)), Function.Surjective f := by
-- proof
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


-- created on 2026-10-20
-- updated on 2026-10-26
