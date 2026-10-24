import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheCyclicQuadrature
open StatMech StatMech.FrontierD


/--
[sixVertexCyclicRootPartition_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_zero_eq
  {n : Nat}
  {p : Fin (n + 1) → Real} :
-- imply
  sixVertexCyclicRootPartition p 0 = p (Fin.last n) - 2 * Real.pi := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_zero p

/--
[sixVertexCyclicRootPartition_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_succ_eq
  {n k : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hk : k <= n) :
-- imply
  sixVertexCyclicRootPartition p (k + 1) = p ⟨k, Nat.lt_succ_of_le hk⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_succ p hk

/--
[sixVertexCyclicRootPartition_end](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_end_eq
  {n : Nat}
  {p : Fin (n + 1) → Real} :
-- imply
  sixVertexCyclicRootPartition p (n + 1) = p (Fin.last n) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_end p

/--
[sixVertexCyclicRootPartition_ordered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_ordered_eq
  {n : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hopen : SixVertexOpenRootSimplex p) :
-- imply
  ∀ k < n + 1, sixVertexCyclicRootPartition p k <= sixVertexCyclicRootPartition p (k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_ordered hopen

/--
[sixVertexCyclicRootPartition_mesh_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_mesh_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  ∀ k < n + 1, sixVertexCyclicRootPartition p (k + 1) - sixVertexCyclicRootPartition p k <= 1 / ((N : Real) * sixVertexTailFiniteDensityFloor c) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_mesh_tail hc htail hN hhalf hopen hsol

/--
[sixVertexCyclicRootPartition_densityMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma sixVertexCyclicRootPartition_densityMass_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  ∀ k < n + 1, ∫ x in sixVertexCyclicRootPartition p k.. sixVertexCyclicRootPartition p (k + 1), sixVertexFiniteRootDensity c N (n + 1) p x = 1 / N := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicRootPartition_densityMass hc hN hhalf hsol

/--
[abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {mesh : Real}
  {f : Real → Real}
  {C : NNReal}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hcount : n + 1 ≤ N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hmesh : ∀ k < n + 1, sixVertexCyclicRootPartition p (k + 1) - sixVertexCyclicRootPartition p k ≤ mesh)
  (hf : Continuous f)
  (hlip : LipschitzWith C f) :
-- imply
  |∑ k ∈ Finset.range (n + 1), (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) - ∫ x in sixVertexCyclicRootPartition p 0.. sixVertexCyclicRootPartition p (n + 1), f x * sixVertexFiniteRootDensity c N (n + 1) p x| ≤ (C : Real) * sixVertexFiniteRootDensityUniformBound c * mesh * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_of_mesh hc hN hcount hhalf hopen hsol hmesh hf hlip

/--
[abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCyclicQuadrature.lean)
-/
@[path]
private lemma abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_tail_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {f : Real → Real}
  {C : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hN : 0 < N)
  (hhalf : N = 2 * (n + 1))
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p)
  (hf : Continuous f)
  (hlip : LipschitzWith C f) :
-- imply
  |∑ k ∈ Finset.range (n + 1), (1 / (N : Real)) * f (sixVertexCyclicRootPartition p k) - ∫ x in sixVertexCyclicRootPartition p 0.. sixVertexCyclicRootPartition p (n + 1), f x * sixVertexFiniteRootDensity c N (n + 1) p x| <= (C : Real) * sixVertexFiniteRootDensityUniformBound c * (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_cyclicBetheEndpointSum_sub_finiteDensityIntegral_le_tail hc htail hN hhalf hopen hsol hf hlip


-- created on 2026-10-23
