import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenRootOffsetIncrement
open StatMech StatMech.FrontierD


/--
[abs_sixVertexEvenChargeBetheOffset_sub_le_invWidth_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenRootOffsetIncrement.lean)
-/
@[path]
private lemma abs_sixVertexEvenChargeBetheOffset_sub_le_invWidth_tail_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) (htail : 2 < sixVertexAnisotropyMagnitude c) (s k : Nat) (j0 j1 : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)) (hij : j1.val = j0.val + 1), |sixVertexEvenChargeBetheOffset hc s k j1 - sixVertexEvenChargeBetheOffset hc s k j0| <= (sixVertexRootGapFirstOrderConstant c (sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) + sixVertexRootGapFirstOrderConstant c (sixVertexFixedChargeDensityInvWidthConstant c 0) + ((sixVertexFiniteRootDensityLipschitzConstant c : Real) / sixVertexTailFiniteDensityFloor c ^ 2) * (Real.pi * (sixVertexFixedChargeDensityInvWidthConstant c 0 + sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) / (((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) * sixVertexTailFiniteDensityFloor c))) / sixVertexFourWidth (2 * s) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexEvenChargeBetheOffset_sub_le_invWidth_tail


-- created on 2026-10-23
