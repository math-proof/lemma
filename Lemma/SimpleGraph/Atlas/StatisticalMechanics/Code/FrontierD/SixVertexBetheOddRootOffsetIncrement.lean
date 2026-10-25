import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddRootOffsetIncrement
open StatMech StatMech.FrontierD


/--
[abs_sixVertexOddChargeBetheOffset_sub_le_invWidth_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddRootOffsetIncrement.lean)
-/
@[path]
private lemma abs_sixVertexOddChargeBetheOffset_sub_le_invWidth_tail_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) (htail : 2 < sixVertexAnisotropyMagnitude c) (s k : Nat) (j0 j1 : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)) (hij : j1.val = j0.val + 1), |sixVertexOddChargeBetheOffset hc s k j1 - sixVertexOddChargeBetheOffset hc s k j0| <= (sixVertexRootGapFirstOrderConstant c (sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) + sixVertexRootGapFirstOrderConstant c (sixVertexFixedChargeDensityInvWidthConstant c 0) + ((sixVertexFiniteRootDensityLipschitzConstant c : Real) / sixVertexTailFiniteDensityFloor c ^ 2) * ((((1 / 2 : Real) + Real.pi * (sixVertexFixedChargeDensityInvWidthConstant c 0 + sixVertexFixedChargeDensityInvWidthConstant c (2 * s + 1)) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / sixVertexTailFiniteDensityFloor c) + (1 / sixVertexTailFiniteDensityFloor c) / 2)) / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddChargeBetheOffset_sub_le_invWidth_tail


-- created on 2026-10-23
