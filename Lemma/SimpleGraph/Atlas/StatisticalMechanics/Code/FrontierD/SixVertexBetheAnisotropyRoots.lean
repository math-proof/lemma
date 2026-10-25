import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheAnisotropyRoots.Part4
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[tendsto_sixVertexTheta_sub_linear_atTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean)
-/
@[path]
private lemma tendsto_sixVertexTheta_sub_linear_atTop_eq
-- given
  (x y : Real -> Real) :
-- imply
  Tendsto (fun c => sixVertexTheta c (x c) (y c) - (y c - x c)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexTheta_sub_linear_atTop x y

/--
[sixVertexHalfFilledBetheRootAt_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledBetheRootAt_eq_eq
  {c : Real}
  {k : Nat}
  {j : Fin ((k + 1) + (k + 1))}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexHalfFilledBetheRootAt k j c = sixVertexHalfFilledBetheRoots hc k j := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledBetheRootAt_eq hc k j

/--
[sixVertexHalfFilledLimitingRoot_mem_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledLimitingRoot_mem_Ioo_eq
  {k : Nat}
  {j : Fin ((k + 1) + (k + 1))} :
-- imply
  sixVertexHalfFilledLimitingRoot k j ∈ Set.Ioo (-Real.pi) Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledLimitingRoot_mem_Ioo k j

/--
[sixVertexHalfFilledLimitingPhase_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean)
-/
@[path]
private lemma sixVertexHalfFilledLimitingPhase_injective_eq
  {k : Nat} :
-- imply
  Function.Injective (sixVertexHalfFilledLimitingPhase k) := by
-- proof
  apply StatMech.FrontierD.sixVertexHalfFilledLimitingPhase_injective k

/--
[tendsto_sixVertexHalfFilledBetheRootAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledBetheRootAt_eq
  {k : Nat}
  {j : Fin ((k + 1) + (k + 1))} :
-- imply
  Tendsto (sixVertexHalfFilledBetheRootAt k j) atTop (nhds (sixVertexHalfFilledLimitingRoot k j)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledBetheRootAt k j

/--
[tendsto_sixVertexHalfFilledBethePhaseAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheAnisotropyRoots.lean)
-/
@[path]
private lemma tendsto_sixVertexHalfFilledBethePhaseAt_eq
  {k : Nat}
  {j : Fin ((k + 1) + (k + 1))} :
-- imply
  Tendsto (fun c => sixVertexBethePhase (sixVertexHalfFilledBetheRootAt k j c)) atTop (nhds (sixVertexHalfFilledLimitingPhase k j)) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexHalfFilledBethePhaseAt k j


-- created on 2026-10-23
