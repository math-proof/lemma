import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP3Domain
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_P3_support_of_domainResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP3Domain.lean)
-/
@[path]
private lemma shb_P3_support_of_domainResummation_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {p : H.Path x y}
-- given
  (hHG : H ≤ G)
  (hresum : shb_P3DomainResummation H G hHG β J p) :
-- imply
  shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p := by
-- proof
  apply StatMech.Sharpness.shb_P3_support_of_domainResummation H G hHG β J p hresum

/--
[shb_P3DomainResummation_of_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP3Domain.lean)
-/
@[path]
private lemma shb_P3DomainResummation_of_support_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {p : H.Path x y}
-- given
  (hHG : H ≤ G)
  (hP3 : shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p) :
-- imply
  shb_P3DomainResummation H G hHG β J p := by
-- proof
  apply StatMech.Sharpness.shb_P3DomainResummation_of_support H G hHG β J p hP3

/--
[shb_P3_support_iff_domainResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP3Domain.lean)
-/
@[path]
private lemma shb_P3_support_iff_domainResummation_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {p : H.Path x y}
-- given
  (hHG : H ≤ G) :
-- imply
  shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p ↔ shb_P3DomainResummation H G hHG β J p := by
-- proof
  apply StatMech.Sharpness.shb_P3_support_iff_domainResummation H G hHG β J p

/--
[shb_backboneNumSupport_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP3Domain.lean)
-/
@[path]
private lemma shb_backboneNumSupport_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {p : G.Path x y}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ shb_backboneNumSupport G β J x y p := by
-- proof
  apply StatMech.Sharpness.shb_backboneNumSupport_nonneg G β J hβ hJ x y p

/--
[shb_P3_support_of_fiber_partition_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneP3Domain.lean)
-/
@[path]
private lemma shb_P3_support_of_fiber_partition_bounds_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {p : H.Path x y}
  {c : ℝ}
-- given
  (hHG : H ≤ G)
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hfiber : shb_backboneNumSupport G β J x y (shb_pathMapLe hHG p) ≤ c * shb_backboneNumSupport H β J x y p)
  (hpartition : c * currentSum H β J ∅ ≤ currentSum G β J ∅) :
-- imply
  shb_rhoSupport G β J x y (shb_pathMapLe hHG p) ≤ shb_rhoSupport H β J x y p := by
-- proof
  apply StatMech.Sharpness.shb_P3_support_of_fiber_partition_bounds H G hHG β J hβ hJ p c hfiber hpartition


-- created on 2026-10-23
