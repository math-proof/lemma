import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseConstant.Part2
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBetheL_add_M](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBetheL_add_M_eq
  {c : Real}
  {z : Complex}
-- given
  (hz : z ≠ 1) :
-- imply
  sixVertexBetheL c z + sixVertexBetheM c z = 2 - c ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_add_M hz

/--
[sixVertexBetheL_mul_one_sub_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBetheL_mul_one_sub_pow_eq
  {c : Real}
  {z : Complex}
  {N : Nat}
-- given
  (hz : z ≠ 1) :
-- imply
  sixVertexBetheL c z * (1 - z ^ N) = (1 - z ^ N) + (c : Complex) ^ 2 * z * ∑ k ∈ Finset.range N, z ^ k := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_mul_one_sub_pow hz N

/--
[sixVertexBetheM_mul_one_sub_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBetheM_mul_one_sub_pow_eq
  {c : Real}
  {z : Complex}
  {N : Nat}
-- given
  (hz : z ≠ 1) :
-- imply
  sixVertexBetheM c z * (1 - z ^ N) = (1 - z ^ N) - (c : Complex) ^ 2 * ∑ k ∈ Finset.range N, z ^ k := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_mul_one_sub_pow hz N

/--
[sixVertexBetheL_phase_mul_one_sub_pow_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBetheL_phase_mul_one_sub_pow_tendsto_eq
  {c : Real}
  {N : Nat} :
-- imply
  Tendsto (fun eps : Real => sixVertexBetheL c (sixVertexBethePhase eps) * (1 - sixVertexBethePhase eps ^ N)) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((c : Complex) ^ 2 * N)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_phase_mul_one_sub_pow_tendsto c N

/--
[sixVertexBetheM_phase_mul_one_sub_pow_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBetheM_phase_mul_one_sub_pow_tendsto_eq
  {c : Real}
  {N : Nat} :
-- imply
  Tendsto (fun eps : Real => sixVertexBetheM c (sixVertexBethePhase eps) * (1 - sixVertexBethePhase eps ^ N)) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds (-((c : Complex) ^ 2 * N))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_phase_mul_one_sub_pow_tendsto c N

/--
[sixVertexTheta_zero_exp_eq_neg_L_div_M](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexTheta_zero_exp_eq_neg_L_div_M_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c)
  (hy : sixVertexBethePhase y ≠ 1) :
-- imply
  Complex.exp (Complex.I * sixVertexTheta c 0 y) = -sixVertexBetheL c (sixVertexBethePhase y) / sixVertexBetheM c (sixVertexBethePhase y) := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_zero_exp_eq_neg_L_div_M hc hy

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.puncturedLProduct_eq_MProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma puncturedLProduct_eq_MProduct_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheL c (sixVertexBethePhase (p j))) = ∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j)) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.puncturedLProduct_eq_MProduct hc p hp ell hell hother

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedMonomial_shift_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma perturbedMonomial_shift_sum_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 1)), sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma (sixVertexBetheShiftCoordinates N x)) = ∑ sigma : Equiv.Perm (Fin (n + 1)), (sixVertexBethePhase (p (sigma (Fin.last n))) / sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps (sigma (Fin.last n)))) ^ N * sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedMonomial_shift_sum hc p hp ell eps x

/--
[sixVertexBethePerturbedMProduct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBethePerturbedMProduct_eq_eq
  {n : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real} :
-- imply
  (∏ j, sixVertexBetheM c (sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j))) = sixVertexBetheM c (sixVertexBethePhase eps) * ∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedMProduct_eq c p ell eps

/--
[sixVertexBethePerturbedLProduct_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBethePerturbedLProduct_eq_eq
  {n : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real} :
-- imply
  (∏ j, sixVertexBetheL c (sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j))) = sixVertexBetheL c (sixVertexBethePhase eps) * ∏ j ∈ (Finset.univ.erase ell), sixVertexBetheL c (sixVertexBethePhase (p j)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedLProduct_eq c p ell eps

/--
[sixVertexBethePerturbedBoundaryRatio_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBethePerturbedBoundaryRatio_sum_eq
  {n : Nat}
  {N : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {F : Equiv.Perm (Fin (n + 1)) → Complex}
-- given
  (hell : p ell = 0) :
-- imply
  (∑ sigma, (sixVertexBethePhase (p (sigma (Fin.last n))) / sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps (sigma (Fin.last n)))) ^ N * F sigma) = (∑ sigma, F sigma) + (sixVertexBethePhase eps ^ (-(N : Int)) - 1) * ∑ sigma with sigma (Fin.last n) = ell, F sigma := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedBoundaryRatio_sum p ell hell eps F

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedConstantWordTotal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma perturbedConstantWordTotal_eq_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int}
  {eps : Real}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBethePerturbedConstantWordTotal N c p ell x eps = (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * ((sixVertexBetheM c (sixVertexBethePhase eps) + sixVertexBetheL c (sixVertexBethePhase eps)) * (∑ sigma, sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x) + sixVertexBetheL c (sixVertexBethePhase eps) * (sixVertexBethePhase eps ^ (-(N : Int)) - 1) * ∑ sigma with sigma (Fin.last n) = ell, sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedConstantWordTotal_eq hc p hp ell hell hother x eps

/--
[continuous_sixVertexBethePerturbedIntMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma continuous_sixVertexBethePerturbedIntMonomial_eq
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
  {sigma : Equiv.Perm (Fin n)}
  {x : Fin n → Int} :
-- imply
  Continuous (fun eps : Real => sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePerturbedIntMonomial p ell sigma x

/--
[sixVertexBetheL_phase_mul_zpow_neg_sub_one_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma sixVertexBetheL_phase_mul_zpow_neg_sub_one_tendsto_eq
  {c : Real}
  {N : Nat} :
-- imply
  Tendsto (fun eps : Real => sixVertexBetheL c (sixVertexBethePhase eps) * (sixVertexBethePhase eps ^ (-(N : Int)) - 1)) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((c : Complex) ^ 2 * N)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_phase_mul_zpow_neg_sub_one_tendsto c N

/--
[continuous_sixVertexBethePerturbedWaveSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma continuous_sixVertexBethePerturbedWaveSum_eq
  {n : Nat}
  {c : Real}
  {p : Fin n → Real}
  {ell : Fin n}
  {x : Fin n → Int} :
-- imply
  Continuous (fun eps : Real => ∑ sigma : Equiv.Perm (Fin n), sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePerturbedWaveSum c p ell x

/--
[continuous_sixVertexBethePerturbedBoundarySum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma continuous_sixVertexBethePerturbedBoundarySum_eq
  {n : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int} :
-- imply
  Continuous (fun eps : Real => ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma (Fin.last n) = ell, sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial (sixVertexBethePerturbRoot p ell eps) sigma x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePerturbedBoundarySum c p ell x

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedConstantWordTotal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseConstant.lean)
-/
@[path]
private lemma perturbedConstantWordTotal_tendsto_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  Tendsto (sixVertexBethePerturbedConstantWordTotal N c p ell x) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ( ((2 : Complex) - (c : Complex) ^ 2) * (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * sixVertexCoordinateBetheIntWave c p x + (c : Complex) ^ 2 * N * (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * ∑ sigma with sigma (Fin.last n) = ell, sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial p sigma x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedConstantWordTotal_tendsto hc p hp ell hell hother x


-- created on 2026-10-23
