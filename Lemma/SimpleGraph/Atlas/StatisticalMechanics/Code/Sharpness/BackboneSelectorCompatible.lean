import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSelectorCompatible.Part5
open SimpleGraph Finset StatMech StatMech.Sharpness


/--
[shb_supportPathOrder_mapLe_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_supportPathOrder_mapLe_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {x y : V}
  {p q : H.Path x y}
-- given
  (hHG : H ≤ G) :
-- imply
  (p.1.mapLe hHG).support < (q.1.mapLe hHG).support ↔ p.1.support < q.1.support := by
-- proof
  apply StatMech.Sharpness.shb_supportPathOrder_mapLe_iff hHG p q

/--
[shb_pathMapLe_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_pathMapLe_injective_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {x y : V}
-- given
  (hHG : H ≤ G) :
-- imply
  Function.Injective (shb_pathMapLe hHG : H.Path x y → G.Path x y) := by
-- proof
  apply StatMech.Sharpness.shb_pathMapLe_injective hHG

/--
[shb_mapLe_restrictBackbonePath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_mapLe_restrictBackbonePath_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {p : G.Path x y}
-- given
  (hHG : H ≤ G)
  (hSupp : shb_CurrentSupportedOn H n)
  (hp : shb_IsBackboneOf G n x y p) :
-- imply
  (⟨(shb_restrictBackbonePath hHG n hSupp p hp).1.mapLe hHG, (shb_restrictBackbonePath hHG n hSupp p hp).2.mapLe hHG⟩ : G.Path x y) = p := by
-- proof
  apply StatMech.Sharpness.shb_mapLe_restrictBackbonePath hHG n hSupp p hp

/--
[shb_restrictBackbonePath_isBackbone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_restrictBackbonePath_isBackbone_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
  {p : G.Path x y}
-- given
  (hHG : H ≤ G)
  (hSupp : shb_CurrentSupportedOn H n)
  (hp : shb_IsBackboneOf G n x y p) :
-- imply
  shb_IsBackboneOf H n x y (shb_restrictBackbonePath hHG n hSupp p hp) := by
-- proof
  apply StatMech.Sharpness.shb_restrictBackbonePath_isBackbone hHG n hSupp p hp

/--
[shb_mapLe_isBackboneOf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_mapLe_isBackboneOf_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  {n : Current V}
  {x y : V}
  {p : H.Path x y}
-- given
  (hHG : H ≤ G)
  (hp : shb_IsBackboneOf H n x y p) :
-- imply
  shb_IsBackboneOf G n x y ⟨p.1.mapLe hHG, p.2.mapLe hHG⟩ := by
-- proof
  apply StatMech.Sharpness.shb_mapLe_isBackboneOf hHG n p hp

/--
[shb_backboneSet_nonempty_iff_of_supported](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_backboneSet_nonempty_iff_of_supported_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
-- given
  (hHG : H ≤ G)
  (hSupp : shb_CurrentSupportedOn H n) :
-- imply
  (shb_backboneSet H n x y).Nonempty ↔ (shb_backboneSet G n x y).Nonempty := by
-- proof
  apply StatMech.Sharpness.shb_backboneSet_nonempty_iff_of_supported hHG n hSupp x y

/--
[shb_backboneSelectSupport_mapLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_backboneSelectSupport_mapLe_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {n : Current V}
  {x y : V}
-- given
  (hHG : H ≤ G)
  (hSupp : shb_CurrentSupportedOn H n) :
-- imply
  Option.map (shb_pathMapLe hHG) (shb_backboneSelectSupport H n x y) = shb_backboneSelectSupport G n x y := by
-- proof
  apply StatMech.Sharpness.shb_backboneSelectSupport_mapLe hHG n hSupp x y

/--
[shb_ofEdgeFun_supportedOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_ofEdgeFun_supportedOn_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H : SimpleGraph V}
  [DecidableRel H.Adj]
  {m : H.edgeFinset → ℕ} :
-- imply
  shb_CurrentSupportedOn H (ofEdgeFun H m) := by
-- proof
  apply StatMech.Sharpness.shb_ofEdgeFun_supportedOn H m

/--
[shb_backboneSelectSupport_ofEdgeFun_mapLe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_backboneSelectSupport_ofEdgeFun_mapLe_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {m : H.edgeFinset → ℕ}
  {x y : V}
-- given
  (hHG : H ≤ G) :
-- imply
  Option.map (shb_pathMapLe hHG) (shb_backboneSelectSupport H (ofEdgeFun H m) x y) = shb_backboneSelectSupport G (ofEdgeFun H m) x y := by
-- proof
  apply StatMech.Sharpness.shb_backboneSelectSupport_ofEdgeFun_mapLe hHG m x y

/--
[shb_backboneSelectSupport_ofEdgeFun_eq_some_mapLe_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_backboneSelectSupport_ofEdgeFun_eq_some_mapLe_iff_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {H G : SimpleGraph V}
  [DecidableRel H.Adj]
  [DecidableRel G.Adj]
  {m : H.edgeFinset → ℕ}
  {x y : V}
  {p : H.Path x y}
-- given
  (hHG : H ≤ G) :
-- imply
  shb_backboneSelectSupport G (ofEdgeFun H m) x y = some (shb_pathMapLe hHG p) ↔ shb_backboneSelectSupport H (ofEdgeFun H m) x y = some p := by
-- proof
  apply StatMech.Sharpness.shb_backboneSelectSupport_ofEdgeFun_eq_some_mapLe_iff hHG m p

/--
[shb_support_indicator_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_support_indicator_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
  {m : G.edgeFinset → ℕ}
-- given
  (hxy : x ≠ y) :
-- imply
  (if sources G (ofEdgeFun G m) = {x, y} then weight G β J (ofEdgeFun G m) else 0) = ∑ p : G.Path x y, if sources G (ofEdgeFun G m) = {x, y} ∧ shb_backboneSelectSupport G (ofEdgeFun G m) x y = some p then weight G β J (ofEdgeFun G m) else 0 := by
-- proof
  apply StatMech.Sharpness.shb_support_indicator_eq_sum G β J hxy m

/--
[shb_currentSum_eq_sum_backboneNumSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_currentSum_eq_sum_backboneNumSupport_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hxy : x ≠ y) :
-- imply
  currentSum G β J {x, y} = ∑ p : G.Path x y, shb_backboneNumSupport G β J x y p := by
-- proof
  apply StatMech.Sharpness.shb_currentSum_eq_sum_backboneNumSupport G β J hβ hJ hxy

/--
[shb_P1_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_P1_support_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hxy : x ≠ y) :
-- imply
  expectationJ G β J {x, y} = ∑ p : G.Path x y, shb_rhoSupport G β J x y p := by
-- proof
  apply StatMech.Sharpness.shb_P1_support G β J hβ hJ hxy

/--
[shb_P2_support_of_complementResummation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSelectorCompatible.lean)
-/
@[path]
private lemma shb_P2_support_of_complementResummation_eq
  [Fintype V]
  [DecidableEq V]
  [LinearOrder V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {x z u : V}
  {p₁₂ : G.Path x z}
  {p₁ : G.Path x u}
  {p₂ : H.Path u z}
-- given
  (hresum : shb_P2ComplementResummation G H β J p₁₂ p₁ p₂) :
-- imply
  shb_rhoSupport G β J x z p₁₂ = shb_rhoSupport G β J x u p₁ * shb_rhoSupport H β J u z p₂ := by
-- proof
  apply StatMech.Sharpness.shb_P2_support_of_complementResummation G H β J p₁₂ p₁ p₂ hresum


-- created on 2026-10-23
