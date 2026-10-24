import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheRootOffsetAbstract
open StatMech StatMech.FrontierD


/--
[abs_width_mul_matchedBetheRoot_sub_le_of_weightedDensityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootOffsetAbstract.lean)
-/
@[path]
private lemma abs_width_mul_matchedBetheRoot_sub_le_of_weightedDensityClose_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N) {p : Fin np -> Real} {q : Fin nq -> Real} (hpOpen : SixVertexOpenRootSimplex p) (hqOpen : SixVertexOpenRootSimplex q) (hpSol : SixVertexSatisfiesBetheEquations c N np p) (hqSol : SixVertexSatisfiesBetheEquations c N nq q) {rho : Real -> Real} {E0 Er lower : Real} (hE0 : 0 <= E0) (hEr : 0 <= Er) (hlower : 0 < lower) (hpClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi -> |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N np p x - rho x)| <= E0 / N) (hqClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi -> |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N nq q x - rho x)| <= Er / N) (hqDensity : forall x, lower <= sixVertexFiniteRootDensity c N nq q x) (ip : Fin np) (iq : Fin nq) (hquantum : sixVertexCentralQuantumNumber ip = sixVertexCentralQuantumNumber iq), |(N : Real) * (q iq - p ip)| <= Real.pi * (E0 + Er) / (((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c) * lower) := by
-- proof
  apply StatMech.FrontierD.abs_width_mul_matchedBetheRoot_sub_le_of_weightedDensityClose

/--
[abs_width_mul_BetheRoot_sub_le_of_weightedDensityClose](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootOffsetAbstract.lean)
-/
@[path]
private lemma abs_width_mul_BetheRoot_sub_le_of_weightedDensityClose_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) {N np nq : Nat} (hN : 0 < N) {p : Fin np -> Real} {q : Fin nq -> Real} (hpOpen : SixVertexOpenRootSimplex p) (hqOpen : SixVertexOpenRootSimplex q) (hpSol : SixVertexSatisfiesBetheEquations c N np p) (hqSol : SixVertexSatisfiesBetheEquations c N nq q) {rho : Real -> Real} {E0 Er lower Q : Real} (hE0 : 0 <= E0) (hEr : 0 <= Er) (hlower : 0 < lower) (hQ : 0 <= Q) (hpClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi -> |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N np p x - rho x)| <= E0 / N) (hqClose : forall x, x ∈ Set.Icc (-Real.pi) Real.pi -> |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c N nq q x - rho x)| <= Er / N) (hqDensity : forall x, lower <= sixVertexFiniteRootDensity c N nq q x) (ip : Fin np) (iq : Fin nq) (hquantum : |sixVertexCentralQuantumNumber ip - sixVertexCentralQuantumNumber iq| <= Q), |(N : Real) * (q iq - p ip)| <= (Q + Real.pi * (E0 + Er) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / lower := by
-- proof
  apply StatMech.FrontierD.abs_width_mul_BetheRoot_sub_le_of_weightedDensityClose

/--
[abs_genericOffsetNodalResidual_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRootOffsetAbstract.lean)
-/
@[path]
private lemma abs_genericOffsetNodalResidual_le_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) {N n : Nat} (hN : 0 < N) (hn : n <= N) {p q : Fin n -> Real} {eps boundary : Fin n -> Real} {B : Real} (hB : 0 <= B) (heps : forall j, eps j = (N : Real) * (q j - p j)) (hoffset : forall j, |eps j| <= B) (hcommon : forall i, eps i - boundary i = ∑ j, (sixVertexTheta c (p i) (p j) - sixVertexTheta c (q i) (q j))) (i : Fin n), |eps i - boundary i + (1 / (N : Real)) * ∑ j, ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) / sixVertexThetaDerivativeDenominator c (q i) (q j)) * eps i + (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q i) / sixVertexThetaDerivativeDenominator c (q i) (q j)) * eps j)| <= 4 * sixVertexThetaTaylorBound c * B ^ 2 / N := by
-- proof
  apply StatMech.FrontierD.abs_genericOffsetNodalResidual_le


-- created on 2026-10-23
