import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.DecorationSpinGauge.Part5
open StatMech StatMech.Onsager


/--
[ons_dirPhase_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_dirPhase_one_one_eq
  {mu : Fin 4} :
-- imply
  ons_dirPhase 1 1 mu = 1 := by
-- proof
  apply StatMech.Onsager.ons_dirPhase_one_one mu

/--
[ons_spinVertexGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinVertexGauge_ne_zero_eq
  {L : ℕ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L} :
-- imply
  ons_spinVertexGauge L a b site ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_spinVertexGauge_ne_zero L a b site

/--
[ons_spinPhase_zpow_x_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinPhase_zpow_x_gauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_spinPhase L a ^ ons_dirExponentX d.2 * ons_spinPhase L a ^ (d.1.1.val : ℤ) = (-1 : ℂ) ^ ((a.val : ℤ) * ons_xWrapSign d) * ons_spinPhase L a ^ ((ons_dirStep L d.2 d.1).1.val : ℤ) := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_zpow_x_gauge L a d

/--
[ons_spinPhase_zpow_y_gauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinPhase_zpow_y_gauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_spinPhase L b ^ ons_dirExponentY d.2 * ons_spinPhase L b ^ (d.1.2.val : ℤ) = (-1 : ℂ) ^ ((b.val : ℤ) * ons_yWrapSign d) * ons_spinPhase L b ^ ((ons_dirStep L d.2 d.1).2.val : ℤ) := by
-- proof
  apply StatMech.Onsager.ons_spinPhase_zpow_y_gauge L b d

/--
[ons_dirPhase_spin_mul_vertexGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_dirPhase_spin_mul_vertexGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_dirPhase (ons_spinPhase L a) (ons_spinPhase L b) d.2 * ons_spinVertexGauge L a b d.1 = ons_spinDartSeamSign a b d * ons_spinVertexGauge L a b (ons_dirStep L d.2 d.1) := by
-- proof
  apply StatMech.Onsager.ons_dirPhase_spin_mul_vertexGauge L a b d

/--
[ons_neg_one_zpow_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_neg_one_zpow_sq_eq
  {m : ℤ} :
-- imply
  ((-1 : ℂ) ^ m) ^ 2 = 1 := by
-- proof
  apply StatMech.Onsager.ons_neg_one_zpow_sq m

/--
[ons_spinDartSeamSign_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinDartSeamSign_rev_eq
  {L : ℕ}
  [Fact (2 < L)]
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_spinDartSeamSign a b (ons_dartRev L d) = ons_spinDartSeamSign a b d := by
-- proof
  apply StatMech.Onsager.ons_spinDartSeamSign_rev L a b d

/--
[ons_spinSeamDecWeight_external](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinSeamDecWeight_external_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {d : ons_Dart L} :
-- imply
  ons_spinSeamDecWeight decWeight a b s(d, ons_dartRev L d) = ons_spinDartSeamSign a b d * decWeight s(d, ons_dartRev L d) := by
-- proof
  apply StatMech.Onsager.ons_spinSeamDecWeight_external L decWeight a b d

/--
[ons_spinSeamDecWeight_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinSeamDecWeight_chain_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {i : Fin 3} :
-- imply
  ons_spinSeamDecWeight decWeight a b (ons_decChainEdge site i) = decWeight (ons_decChainEdge site i) := by
-- proof
  apply StatMech.Onsager.ons_spinSeamDecWeight_chain L decWeight a b site i

/--
[ons_loopWeight_diagonalGaugeMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_loopWeight_diagonalGaugeMatrix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  [NeZero n]
  {gauge : E → ℂ}
  {M : Matrix E E ℂ}
  {loop : Fin n → E}
-- given
  (hgauge : ∀ e, gauge e ≠ 0) :
-- imply
  ons_loopWeight (ons_diagonalGaugeMatrix gauge M) loop = ons_loopWeight M loop := by
-- proof
  apply StatMech.Onsager.ons_loopWeight_diagonalGaugeMatrix gauge hgauge M loop

/--
[ons_decTransitionWeight_spinSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decTransitionWeight_spinSeam_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {d₂ d₁ : ons_Dart L} :
-- imply
  ons_decTransitionWeight L (ons_spinSeamDecWeight decWeight a b) d₂ d₁ = ons_spinDartSeamSign a b d₁ * ons_decTransitionWeight L decWeight d₂ d₁ := by
-- proof
  apply StatMech.Onsager.ons_decTransitionWeight_spinSeam L decWeight a b d₂ d₁

/--
[ons_KWmatDecorationWeightedPhase_spinGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_KWmatDecorationWeightedPhase_spinGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega : ℂ} :
-- imply
  ons_KWmatDecorationWeightedPhase L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b) = ons_diagonalGaugeMatrix (fun d : ons_Dart L ↦ ons_spinVertexGauge L a b d.1) (ons_KWmatDecorationWeightedPhase L (ons_spinSeamDecWeight decWeight a b) omega 1 1) := by
-- proof
  apply StatMech.Onsager.ons_KWmatDecorationWeightedPhase_spinGauge L decWeight a b omega

/--
[ons_decMiddleU_spinSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decMiddleU_spinSeam_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleU L (ons_spinSeamDecWeight decWeight a b) omega site = ons_decMiddleU L decWeight omega site := by
-- proof
  apply StatMech.Onsager.ons_decMiddleU_spinSeam L decWeight a b omega site

/--
[ons_decMiddleSourceFactor_spinSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decMiddleSourceFactor_spinSeam_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {mu : Fin 4} :
-- imply
  ons_decMiddleSourceFactor (ons_spinSeamDecWeight decWeight a b) site mu = ons_decMiddleSourceFactor decWeight site mu := by
-- proof
  apply StatMech.Onsager.ons_decMiddleSourceFactor_spinSeam L decWeight a b site mu

/--
[ons_decMiddleV_spinGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decMiddleV_spinGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleV L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b) site = fun side d ↦ ons_spinVertexGauge L a b site * ons_decMiddleV L (ons_spinSeamDecWeight decWeight a b) omega 1 1 site side d * (ons_spinVertexGauge L a b d.1)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_decMiddleV_spinGauge L decWeight a b omega site

/--
[ons_spinSeamDecWeight_scale_chain_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_spinSeamDecWeight_scale_chain_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L}
  {t : ℂ} :
-- imply
  ons_spinSeamDecWeight (ons_scaleDecEdgeWeight decWeight (ons_decChainEdge site 1) t) a b = ons_scaleDecEdgeWeight (ons_spinSeamDecWeight decWeight a b) (ons_decChainEdge site 1) t := by
-- proof
  apply StatMech.Onsager.ons_spinSeamDecWeight_scale_chain_one L decWeight a b site t

/--
[ons_decMiddleStateGauge_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decMiddleStateGauge_ne_zero_eq
  {L : ℕ}
  {a b : Fin 2}
  {site : ZMod L × ZMod L} :
-- imply
  ∀ state, ons_decMiddleStateGauge L a b site state ≠ 0 := by
-- proof
  apply StatMech.Onsager.ons_decMiddleStateGauge_ne_zero L a b site

/--
[ons_decMiddleU_spinGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decMiddleU_spinGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega : ℂ}
  {site : ZMod L × ZMod L}
  {d : ons_Dart L}
  {side : Fin 2} :
-- imply
  ons_decMiddleU L decWeight omega site d side = ons_spinVertexGauge L a b d.1 * ons_decMiddleU L (ons_spinSeamDecWeight decWeight a b) omega site d side * (ons_spinVertexGauge L a b site)⁻¹ := by
-- proof
  apply StatMech.Onsager.ons_decMiddleU_spinGauge L decWeight a b omega site d side

/--
[ons_decMiddleAugmented_spinGauge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationSpinGauge.lean)
-/
@[path]
private lemma ons_decMiddleAugmented_spinGauge_eq
  {L : ℕ}
  [Fact (2 < L)]
  {decWeight : ons_DecEdge L → ℂ}
  {a b : Fin 2}
  {omega t : ℂ}
  {site : ZMod L × ZMod L} :
-- imply
  ons_decMiddleAugmented L decWeight omega (ons_spinPhase L a) (ons_spinPhase L b) t site = ons_diagonalGaugeMatrix (ons_decMiddleStateGauge L a b site) (ons_decMiddleAugmented L (ons_spinSeamDecWeight decWeight a b) omega 1 1 t site) := by
-- proof
  apply StatMech.Onsager.ons_decMiddleAugmented_spinGauge L decWeight a b omega t site


-- created on 2026-10-23
