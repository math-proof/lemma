import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheFixedChargeRoots.Part3
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexFixedChargeBetheParticleCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheParticleCount_eq_eq
  {r k : Nat} :
-- imply
  sixVertexFixedChargeBetheParticleCount r k = r + 2 * (k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheParticleCount_eq r k

/--
[sixVertexFixedChargeBetheParticleCount_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheParticleCount_pos_eq
  {r k : Nat} :
-- imply
  0 < sixVertexFixedChargeBetheParticleCount r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheParticleCount_pos r k

/--
[sixVertexFixedChargeBetheParticleCount_twice_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheParticleCount_twice_le_eq
  {r k : Nat} :
-- imply
  2 * sixVertexFixedChargeBetheParticleCount r k <= sixVertexFourWidth r k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheParticleCount_twice_le r k

/--
[sixVertexFixedChargeBetheRoots_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_mem_open_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexOpenRootSimplex (sixVertexFixedChargeBetheRoots hc r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_mem_open hc r k

/--
[sixVertexFixedChargeBetheRoots_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_is_solution_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesBetheEquations c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_is_solution hc r k

/--
[sixVertexFixedChargeBetheRoots_is_multiplicativeSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_is_multiplicativeSolution_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexSatisfiesMultiplicativeBetheEquations c (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) (sixVertexFixedChargeBetheRoots hc r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_is_multiplicativeSolution hc r k

/--
[sixVertexFixedChargeBetheRoots_sum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_sum_eq_zero_eq
  {c : Real}
  {r k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∑ j, sixVertexFixedChargeBetheRoots hc r k j = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_sum_eq_zero hc r k

/--
[sixVertexFixedChargeBetheRoot_add_empiricalTheta_eq_quantum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoot_add_empiricalTheta_eq_quantum_eq
  {c : Real}
  {r k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexFixedChargeBetheRoots hc r k j + (∑ l, sixVertexTheta c (sixVertexFixedChargeBetheRoots hc r k j) (sixVertexFixedChargeBetheRoots hc r k l)) / (sixVertexFourWidth r k : Real) = 2 * Real.pi * sixVertexCentralQuantumNumber j / (sixVertexFourWidth r k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoot_add_empiricalTheta_eq_quantum hc r k j

/--
[sixVertexFixedChargeBetheRoots_quantumSpacing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_quantumSpacing_eq
  {c : Real}
  {r k : Nat}
  {i j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c)
  (hij : i < j) :
-- imply
  2 * Real.pi * (sixVertexCentralQuantumNumber j - sixVertexCentralQuantumNumber i) < (sixVertexFourWidth r k : Real) * (sixVertexFixedChargeBetheRoots hc r k j - sixVertexFixedChargeBetheRoots hc r k i) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_quantumSpacing hc r k hij

/--
[sixVertexFixedChargeBetheParticleDensity_tendsto_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheParticleDensity_tendsto_half_eq
  {r : Nat} :
-- imply
  Tendsto (fun k : Nat => (sixVertexFixedChargeBetheParticleCount r k : Real) / (sixVertexFourWidth r k : Real)) atTop (nhds (1 / 2 : Real)) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheParticleDensity_tendsto_half r

/--
[sixVertexFixedChargeBetheRoots_phase_ne_one_of_even_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_phase_ne_one_of_even_charge_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount r k)}
-- given
  (hc : 2 < c)
  (hr : Even r) :
-- imply
  sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k j) ≠ 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_phase_ne_one_of_even_charge hc hr k j

/--
[sixVertexFixedChargeBetheRoots_physicalEigenrelation_of_even_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_physicalEigenrelation_of_even_charge_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Even r) :
-- imply
  SixVertexCoordinateBetheEigenrelation (N := sixVertexFourWidth r k) c (sixVertexFixedChargeBetheRoots hc r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_physicalEigenrelation_of_even_charge hc hr k

/--
[sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  sixVertexFixedChargeBetheRoots hc r k (sixVertexFixedChargeBetheCentralIndex r k) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_central_eq_zero_of_odd_charge hc hr k

/--
[sixVertexFixedChargeBetheRoots_central_phase_eq_one_of_odd_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheFixedChargeRoots.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_central_phase_eq_one_of_odd_charge_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  sixVertexBethePhase (sixVertexFixedChargeBetheRoots hc r k (sixVertexFixedChargeBetheCentralIndex r k)) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_central_phase_eq_one_of_odd_charge hc hr k


-- created on 2026-10-23
