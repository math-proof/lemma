import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
open SimpleGraph Finset StatMech StatMech.Sharpness StatMech.Sharpness.shb_BackboneExplorationDomain


/--
[shb_AmbientSegment.toPath_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma toPath_edges_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H : SimpleGraph V}
  {s : shb_AmbientSegment V}
-- given
  (h : s.Supported H) :
-- imply
  (s.toPath H h).1.edges = s.2.2.1.edges := by
-- proof
  apply StatMech.Sharpness.shb_AmbientSegment.toPath_edges H s h

/--
[shb_explorationAdvance_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_explorationAdvance_mono_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H K : SimpleGraph V}
  {s : shb_AmbientSegment V}
-- given
  (hHK : H ≤ K) :
-- imply
  shb_explorationAdvance H s ≤ shb_explorationAdvance K s := by
-- proof
  apply StatMech.Sharpness.shb_explorationAdvance_mono hHK s

/--
[shb_segmentRho_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_segmentRho_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {H : SimpleGraph V}
  {s : shb_AmbientSegment V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ shb_segmentRho β J H s := by
-- proof
  apply StatMech.Sharpness.shb_segmentRho_nonneg β J hβ hJ H s

/--
[supported_deleteEdges_of_compatible](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma supported_deleteEdges_of_compatible_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_BackboneExplorationDomain V}
  {H : SimpleGraph V}
  {s t : shb_AmbientSegment V}
-- given
  (ht : t.Supported H)
  (hst : compatible s t) :
-- imply
  t.Supported (H.deleteEdges s.edgeSet) := by
-- proof
  apply StatMech.Sharpness.shb_BackboneExplorationDomain.supported_deleteEdges_of_compatible d ht hst

/--
[advance_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma advance_mono_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_BackboneExplorationDomain V}
  {d k : shb_BackboneExplorationDomain V}
  {s : shb_AmbientSegment V}
-- given
  (hdk : d ≤ k) :
-- imply
  advance d s ≤ advance k s := by
-- proof
  apply StatMech.Sharpness.shb_BackboneExplorationDomain.advance_mono d hdk s

/--
[amplitude_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma amplitude_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_BackboneExplorationDomain V}
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {d : shb_BackboneExplorationDomain V}
  {s : shb_AmbientSegment V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ amplitude β J d s := by
-- proof
  apply StatMech.Sharpness.shb_BackboneExplorationDomain.amplitude_nonneg d β J hβ hJ d s

/--
[toPath_mapLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma toPath_mapLe_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_BackboneExplorationDomain V}
  {H K : SimpleGraph V}
  {s : shb_AmbientSegment V}
-- given
  (hHK : H ≤ K)
  (hH : s.Supported H)
  (hK : s.Supported K) :
-- imply
  shb_pathMapLe hHK (s.toPath H hH) = s.toPath K hK := by
-- proof
  apply StatMech.Sharpness.shb_BackboneExplorationDomain.toPath_mapLe d hHK s hH hK

/--
[amplitude_antitone_of_domainResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma amplitude_antitone_of_domainResummation_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {d : shb_BackboneExplorationDomain V}
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {d k : shb_BackboneExplorationDomain V}
  {s : shb_AmbientSegment V}
-- given
  (hresum : LocalDomainResummation β J)
  (hdk : d ≤ k) :
-- imply
  amplitude β J k s ≤ amplitude β J d s := by
-- proof
  apply StatMech.Sharpness.shb_BackboneExplorationDomain.amplitude_antitone_of_domainResummation d β J hresum hdk s

/--
[shb_segment_unrestricted_cut_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_segment_unrestricted_cut_factor_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H : SimpleGraph V}
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {s : shb_AmbientSegment V} :
-- imply
  shb_fullWeightMass H β J = shb_cutLeftMass H β J (shb_segmentCut H s) * shb_cutRightMass H β J (shb_segmentCut H s) := by
-- proof
  apply StatMech.Sharpness.shb_segment_unrestricted_cut_factor H β J s

/--
[shb_segmentRho_eq_num_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_segmentRho_eq_num_div_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V} :
-- imply
  shb_BackboneExplorationDomain.amplitude β J d s = shb_segmentNum β J d s / currentSum d.graph β J ∅ := by
-- proof
  apply StatMech.Sharpness.shb_segmentRho_eq_num_div β J d s

/--
[shb_normalizedExplorationRho_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_normalizedExplorationRho_nil_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {fiberMass : shb_ExplorationFiberMass V}
  {d : shb_ExplorationDomain V}
-- given
  (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass) :
-- imply
  shb_normalizedExplorationRho β J fiberMass d [] = 1 := by
-- proof
  apply StatMech.Sharpness.shb_normalizedExplorationRho_nil β J fiberMass hcut d

/--
[shb_normalizedExplorationRho_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_normalizedExplorationRho_cons_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {fiberMass : shb_ExplorationFiberMass V}
  {d : shb_ExplorationDomain V}
  {s : shb_ExplorationSegment V}
  {ss : List (shb_ExplorationSegment V)}
-- given
  (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass) :
-- imply
  shb_normalizedExplorationRho β J fiberMass d (s :: ss) = shb_BackboneExplorationDomain.amplitude β J d s * shb_normalizedExplorationRho β J fiberMass (shb_BackboneExplorationDomain.advance d s) ss := by
-- proof
  apply StatMech.Sharpness.shb_normalizedExplorationRho_cons β J fiberMass hcut d s ss

/--
[shb_randomCurrent_rho_eq_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationRealization.lean)
-/
@[path]
private lemma shb_randomCurrent_rho_eq_weight_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {fiberMass : shb_ExplorationFiberMass V}
  {d : shb_ExplorationDomain V}
  {word : List (shb_ExplorationSegment V)}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hdom : shb_BackboneExplorationDomain.LocalDomainResummation β J)
  (hcut : shb_LocalSelectorFiberCutResummation β J fiberMass) :
-- imply
  shb_normalizedExplorationRho β J fiberMass d word = (shb_BackboneExplorationDomain.kernel β J hβ hJ hdom).weight d word := by
-- proof
  apply StatMech.Sharpness.shb_randomCurrent_rho_eq_weight β J hβ hJ hdom fiberMass hcut d word


-- created on 2026-10-23
