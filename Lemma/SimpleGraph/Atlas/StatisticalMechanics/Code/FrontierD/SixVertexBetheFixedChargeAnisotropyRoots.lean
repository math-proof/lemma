import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeAnisotropyRoots.Part4
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeBetheComplementCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheComplementCount_eq_eq
  {r k : Nat} :
-- imply
  sixVertexFixedChargeBetheComplementCount r k = 3 * r + 2 * (k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheComplementCount_eq r k

/--
[sixVertexFixedChargeBetheComplementCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheComplementCount_pos_eq
  {r k : Nat} :
-- imply
  0 < sixVertexFixedChargeBetheComplementCount r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheComplementCount_pos r k

/--
[sixVertexFixedChargeBetheRootAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRootAt_eq_eq
  {c : Real}
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexFixedChargeBetheRootAt r k j c = sixVertexFixedChargeBetheRoots hc r k j := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRootAt_eq hc r k j

/--
[sixVertexFixedChargeLimitingRoot_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingRoot_mem_Ioo_eq
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  sixVertexFixedChargeLimitingRoot r k j ∈ Set.Ioo (-Real.pi) Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingRoot_mem_Ioo r k j

/--
[sixVertexFixedChargeLimitingPhase_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeLimitingPhase_injective_eq
  {r k : Nat} :
-- imply
  Function.Injective (sixVertexFixedChargeLimitingPhase r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeLimitingPhase_injective r k

/--
[tendsto_sixVertexFixedChargeBetheRootAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeBetheRootAt_eq
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  Tendsto (sixVertexFixedChargeBetheRootAt r k j) atTop (nhds (sixVertexFixedChargeLimitingRoot r k j)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeBetheRootAt r k j

/--
[tendsto_sixVertexFixedChargeBethePhaseAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeAnisotropyRoots.lean)
-/
@[path]
private lemma tendsto_sixVertexFixedChargeBethePhaseAt_eq
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)} :
-- imply
  Tendsto (fun c => sixVertexBethePhase (sixVertexFixedChargeBetheRootAt r k j c)) atTop (nhds (sixVertexFixedChargeLimitingPhase r k j)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexFixedChargeBethePhaseAt r k j


-- created on 2026-10-23
