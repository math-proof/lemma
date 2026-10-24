import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.IsingFK.Q2
open StatMech StatMech.IsingFK


/--
[toIsing_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma toIsing_bijective_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Function.Bijective (toIsing (V := V)) := by
-- proof
  apply StatMech.IsingFK.toIsing_bijective

/--
[sigma_eq_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma sigma_eq_iff_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V → Fin 2}
  {x y : V} :
-- imply
  (σ x = σ y) ↔ (toIsing σ x = toIsing σ y) := by
-- proof
  apply StatMech.IsingFK.sigma_eq_iff σ x y

/--
[bond_eq_two_mul_ite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma bond_eq_two_mul_ite_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {x y : V} :
-- imply
  bond s s(x, y) = 2 * (if s x = s y then (1 : ℝ) else 0) - 1 := by
-- proof
  apply StatMech.IsingFK.bond_eq_two_mul_ite s x y

/--
[monoIndicator_toIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma monoIndicator_toIsing_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V → Fin 2}
  {e : Sym2 V} :
-- imply
  monoIndicator σ e = bond (toIsing σ) e / 2 + 1 / 2 := by
-- proof
  apply StatMech.IsingFK.monoIndicator_toIsing σ e

/--
[agreement_eq_bondSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma agreement_eq_bondSum_eq
  [Fintype V]
  [DecidableEq V]
  {σ : V → Fin 2} :
-- imply
  agreement G σ = (∑ e ∈ G.edgeFinset, bond (toIsing σ) e) / 2 + (G.edgeFinset.card : ℝ) / 2 := by
-- proof
  apply StatMech.IsingFK.agreement_eq_bondSum σ

/--
[isingWeight_toIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma isingWeight_toIsing_eq
  [Fintype V]
  [DecidableEq V]
  {βI βP J : ℝ}
  {σ : V → Fin 2}
-- given
  (h : βP * J = 2 * βI) :
-- imply
  isingWeight G βI 0 (toIsing σ) = Real.exp (-βI * G.edgeFinset.card) * pottsWeight G βP J σ := by
-- proof
  apply StatMech.IsingFK.isingWeight_toIsing βI βP J h σ

/--
[isingZ_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma isingZ_eq_eq
  [Fintype V]
  [DecidableEq V]
  {βI βP J : ℝ}
-- given
  (h : βP * J = 2 * βI) :
-- imply
  isingZ G βI 0 = Real.exp (-βI * G.edgeFinset.card) * pottsZ G 2 βP J := by
-- proof
  apply StatMech.IsingFK.isingZ_eq βI βP J h

/--
[isingProb_eq_pottsProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma isingProb_eq_pottsProb_eq
  [Fintype V]
  [DecidableEq V]
  {βI βP J : ℝ}
  {σ : V → Fin 2}
-- given
  (h : βP * J = 2 * βI) :
-- imply
  isingProb G βI 0 (toIsing σ) = pottsProb G 2 βP J σ := by
-- proof
  apply StatMech.IsingFK.isingProb_eq_pottsProb βI βP J h σ

/--
[isingProb_eq_pottsProb'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma isingProb_eq_pottsProb'_eq
  [Fintype V]
  [DecidableEq V]
  {βI βP J : ℝ}
  {s : ConfigSpace V}
-- given
  (h : βP * J = 2 * βI) :
-- imply
  isingProb G βI 0 s = pottsProb G 2 βP J ((Equiv.ofBijective _ toIsing_bijective).symm s) := by
-- proof
  apply StatMech.IsingFK.isingProb_eq_pottsProb' βI βP J h s

/--
[pOfBeta_strictMonoOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma pOfBeta_strictMonoOn_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  StrictMonoOn pOfBeta (Set.Ici (0 : ℝ)) := by
-- proof
  apply StatMech.IsingFK.pOfBeta_strictMonoOn

/--
[pOfBeta_mem_Ico](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma pOfBeta_mem_Ico_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ}
-- given
  (hβ : 0 ≤ β) :
-- imply
  pOfBeta β ∈ Set.Ico (0 : ℝ) 1 := by
-- proof
  apply StatMech.IsingFK.pOfBeta_mem_Ico β hβ

/--
[betaOfP_pOfBeta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma betaOfP_pOfBeta_eq
  [Fintype V]
  [DecidableEq V]
  {β : ℝ} :
-- imply
  betaOfP (pOfBeta β) = β := by
-- proof
  apply StatMech.IsingFK.betaOfP_pOfBeta β

/--
[pOfBeta_betaOfP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma pOfBeta_betaOfP_eq
  [Fintype V]
  [DecidableEq V]
  {p : ℝ}
-- given
  (hp : p < 1) :
-- imply
  pOfBeta (betaOfP p) = p := by
-- proof
  apply StatMech.IsingFK.pOfBeta_betaOfP p hp

/--
[pOfBeta_bijOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/IsingFK/Q2.lean)
-/
@[path]
private lemma pOfBeta_bijOn_eq
  [Fintype V]
  [DecidableEq V] :
-- imply
  Set.BijOn pOfBeta (Set.Ici (0 : ℝ)) (Set.Ico (0 : ℝ) 1) := by
-- proof
  apply StatMech.IsingFK.pOfBeta_bijOn


-- created on 2026-10-23
