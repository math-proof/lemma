import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddRootOffsetBound
open StatMech StatMech.FrontierD


/--
[abs_sixVertexOddChargeBetheOffset_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddRootOffsetBound.lean)
-/
@[path]
private lemma abs_sixVertexOddChargeBetheOffset_le_tail_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) (htail : 2 < sixVertexAnisotropyMagnitude c) (s k : Nat) (j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)), |sixVertexOddChargeBetheOffset hc s k j| <= ((1 / 2 : Real) + Real.pi * (sixVertexFixedChargeDensityInvWidthConstant c 0 + sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / sixVertexTailFiniteDensityFloor c := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddChargeBetheOffset_le_tail


-- created on 2026-10-23
