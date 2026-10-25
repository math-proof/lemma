import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenRootOffsetBound
open StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenRootOffsetBound.lean)
-/
@[path]
private lemma sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail_eq
  {c : Real}
  {r : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  0 <= sixVertexFixedChargeDensityInvWidthConstant c r := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeDensityInvWidthConstant_nonneg_tail hc htail r

/--
[abs_sixVertexEvenChargeBetheOffset_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenRootOffsetBound.lean)
-/
@[path]
private lemma abs_sixVertexEvenChargeBetheOffset_le_tail_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  |sixVertexEvenChargeBetheOffset hc s k j| <= Real.pi * (sixVertexFixedChargeDensityInvWidthConstant c 0 + sixVertexFixedChargeDensityInvWidthConstant c (2 * s)) / (((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) * sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexEvenChargeBetheOffset_le_tail hc htail s k j


-- created on 2026-10-23
