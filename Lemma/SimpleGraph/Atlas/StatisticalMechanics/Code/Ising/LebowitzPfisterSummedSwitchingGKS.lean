import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterSummedSwitchingGKS
open Finset StatMech StatMech.Ising StatMech.FrontierA


/--
[lpCurrentSum_gks_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSummedSwitchingGKS.lean)
-/
@[path]
private lemma lpCurrentSum_gks_second_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e) :
-- imply
  currentSum G beta J A * currentSum G beta J B <= currentSum G beta J (A ∆ B) * currentSum G beta J ∅ := by
-- proof
  apply StatMech.Ising.lpCurrentSum_gks_second G beta J hbeta hJ A B

/--
[lpCurrentSum_pair_gks_gap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSummedSwitchingGKS.lean)
-/
@[path]
private lemma lpCurrentSum_pair_gks_gap_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {A : Finset V}
  {u v : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (huv : u ≠ v) :
-- imply
  currentSum G beta J A * currentSum G beta J ∅ - currentSum G beta J (A ∆ {u, v}) * currentSum G beta J {u, v} = sourcePairDisconnSum G beta J A ∅ u v ∧ 0 <= currentSum G beta J A * currentSum G beta J ∅ - currentSum G beta J (A ∆ {u, v}) * currentSum G beta J {u, v} := by
-- proof
  apply StatMech.Ising.lpCurrentSum_pair_gks_gap G beta J hbeta hJ A huv

/--
[lpMatchingCurrentSkewPolynomial_nonpos_iff_centeredGram](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSummedSwitchingGKS.lean)
-/
@[path]
private lemma lpMatchingCurrentSkewPolynomial_nonpos_iff_centeredGram_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : V}
-- given
  (J : Sym2 V -> Real)
  (left right : I -> V)
  (hg : g0 ≠ g1) :
-- imply
  lpMatchingCurrentSkewPolynomial (lpMatchingCurrentA G beta J left right) (lpMatchingCurrentB G beta J left right g0 g1) (lpMatchingCurrentC G beta J g0 g1) (lpMatchingCurrentD G beta J left right) (lpMatchingCurrentE G beta J left right g0 g1) (lpMatchingCurrentZ G beta J) <= 0 ↔ lpMatchingDisconnCenteredGram G beta J left right g0 g1 <= 0 := by
-- proof
  apply StatMech.Ising.lpMatchingCurrentSkewPolynomial_nonpos_iff_centeredGram G beta J left right g0 g1 hg

/--
[grahamEq22_globalGKSDrops_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterSummedSwitchingGKS.lean)
-/
@[path]
private lemma grahamEq22_globalGKSDrops_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {beta : Real}
  {i j k l m : V}
-- given
  (J : Sym2 V -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hil : i ≠ l)
  (him : i ≠ m)
  (hjk : j ≠ k)
  (hjl : j ≠ l)
  (hjm : j ≠ m)
  (hkl : k ≠ l)
  (hkm : k ≠ m)
  (hlm : l ≠ m) :
-- imply
  (0 <= currentSum G beta J {k, l} * grahamFirstRemainderMass G beta J i j k l m - currentSum G beta J ∅ * grahamFirstMixedRemainderMass G beta J i j k l m) ∧ (0 <= (currentSum G beta J {i, m} * currentSum G beta J {j, m}) * grahamSecondRemainderMass G beta J i j k l m - currentSum G beta J ∅ ^ 2 * grahamSecondMixedRemainderMass G beta J i j k l m) := by
-- proof
  apply StatMech.FrontierA.grahamEq22_globalGKSDrops_nonneg G beta J hbeta hJ hij hik hil him hjk hjl hjm hkl hkm hlm


-- created on 2026-10-23
