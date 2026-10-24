import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterFiveCurrentPairing
open Finset StatMech StatMech.Ising


/--
[lpFiveToggle12_orbitAB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle12_orbitAB_eq
  [DecidableEq W]
  {Si Sj T : Finset W} :
-- imply
  lpFiveToggle12 T (lpFiveOrbitABPos Si Sj T) = lpFiveOrbitABNeg Si Sj T := by
-- proof
  apply StatMech.Ising.lpFiveToggle12_orbitAB Si Sj T

/--
[lpFiveToggle12_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle12_involutive_eq
  [DecidableEq W]
  {T : Finset W} :
-- imply
  Function.Involutive (lpFiveToggle12 T) := by
-- proof
  apply StatMech.Ising.lpFiveToggle12_involutive T

/--
[lpFiveToggle14_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle14_involutive_eq
  [DecidableEq W]
  {T : Finset W} :
-- imply
  Function.Involutive (lpFiveToggle14 T) := by
-- proof
  apply StatMech.Ising.lpFiveToggle14_involutive T

/--
[lpFiveToggle23_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle23_involutive_eq
  [DecidableEq W]
  {T : Finset W} :
-- imply
  Function.Involutive (lpFiveToggle23 T) := by
-- proof
  apply StatMech.Ising.lpFiveToggle23_involutive T

/--
[lpFiveToggle12_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle12_total_eq
  [DecidableEq W]
  {T : Finset W}
  {a : LPFiveSourceAllocation W} :
-- imply
  (lpFiveToggle12 T a).total = a.total := by
-- proof
  apply StatMech.Ising.lpFiveToggle12_total T a

/--
[lpFiveToggle14_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle14_total_eq
  [DecidableEq W]
  {T : Finset W}
  {a : LPFiveSourceAllocation W} :
-- imply
  (lpFiveToggle14 T a).total = a.total := by
-- proof
  apply StatMech.Ising.lpFiveToggle14_total T a

/--
[lpFiveToggle23_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle23_total_eq
  [DecidableEq W]
  {T : Finset W}
  {a : LPFiveSourceAllocation W} :
-- imply
  (lpFiveToggle23 T a).total = a.total := by
-- proof
  apply StatMech.Ising.lpFiveToggle23_total T a

/--
[lpFiveToggle14_orbitEF](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle14_orbitEF_eq
  [DecidableEq W]
  {Si Sj T : Finset W} :
-- imply
  lpFiveToggle14 T (lpFiveOrbitEFNeg Si Sj T) = lpFiveOrbitEFPos Si Sj T := by
-- proof
  apply StatMech.Ising.lpFiveToggle14_orbitEF Si Sj T

/--
[lpFiveToggle23_orbitCD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle23_orbitCD_eq
  [DecidableEq W]
  {Si Sj T : Finset W} :
-- imply
  lpFiveToggle23 T (lpFiveOrbitCDNeg Si Sj T) = lpFiveOrbitCDPos Si Sj T := by
-- proof
  apply StatMech.Ising.lpFiveToggle23_orbitCD Si Sj T

/--
[lpFiveToggle14_orbitGH](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpFiveToggle14_orbitGH_eq
  [DecidableEq W]
  {Si Sj T : Finset W} :
-- imply
  lpFiveToggle14 T (lpFiveOrbitGHNeg Si Sj T) = lpFiveOrbitGHPos Si Sj T := by
-- proof
  apply StatMech.Ising.lpFiveToggle14_orbitGH Si Sj T

/--
[lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
  {i j : I}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  let Si := lpMatchingSeamSource left right i let Sj := lpMatchingSeamSource left right j let T := lpMatchingGhostSource g0 g1 let Z := currentSum G beta J ∅ let C := currentSum G beta J T lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j = sourcePairDisconnSum G beta J (Si ∆ Sj ∆ T) ∅ g0 g1 * Z * (Z ^ 2 - C ^ 2) - 2 * currentSum G beta J Si * sourcePairDisconnSum G beta J (Sj ∆ T) ∅ g0 g1 * Z ^ 2 + 2 * sourcePairDisconnSum G beta J (Si ∆ T) ∅ g0 g1 * currentSum G beta J (Sj ∆ T) * C * Z := by
-- proof
  apply StatMech.Ising.lpMatchingFiveCurrentCoefficient_eq_disconnectionResidues G beta J left right g0 g1 hg i j

/--
[lpMatchingDisconnCenteredGram_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingDisconnCenteredGram_eq_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W) :
-- imply
  lpMatchingDisconnCenteredGram G beta J left right g0 g1 = sourcePairDisconnSum G beta J ∅ ∅ g0 g1 * lpMatchingDisconnTwo G beta J left right g0 g1 - 2 * lpMatchingDisconnZero G beta J left right g0 g1 * lpMatchingDisconnOne G beta J left right g0 g1 := by
-- proof
  apply StatMech.Ising.lpMatchingDisconnCenteredGram_eq G beta J left right g0 g1

/--
[lpMatchingDisconnZero_eq_currentGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingDisconnZero_eq_currentGap_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  let T := lpMatchingGhostSource g0 g1 lpMatchingDisconnZero G beta J left right g0 g1 = (∑ i : I, currentSum G beta J (lpMatchingSeamSource left right i)) * currentSum G beta J ∅ - (∑ i : I, currentSum G beta J (lpMatchingSeamSource left right i ∆ T)) * currentSum G beta J T := by
-- proof
  apply StatMech.Ising.lpMatchingDisconnZero_eq_currentGap G beta J left right g0 g1 hg

/--
[lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  let T := lpMatchingGhostSource g0 g1 let Z := currentSum G beta J ∅ let C := currentSum G beta J T (∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j) = Z * ((Z ^ 2 - C ^ 2) * lpMatchingDisconnTwo G beta J left right g0 g1 - 2 * lpMatchingDisconnZero G beta J left right g0 g1 * lpMatchingDisconnOne G beta J left right g0 g1) := by
-- proof
  apply StatMech.Ising.lpMatchingFiveCurrentCoefficient_sum_eq_disconnectionGap G beta J left right g0 g1 hg

/--
[lpMatchingFiveCurrentCoefficient_sum_nonpos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  let T := lpMatchingGhostSource g0 g1 let Z := currentSum G beta J ∅ let C := currentSum G beta J T ((∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j) <= 0) <-> (Z ^ 2 - C ^ 2) * lpMatchingDisconnTwo G beta J left right g0 g1 <= 2 * lpMatchingDisconnZero G beta J left right g0 g1 * lpMatchingDisconnOne G beta J left right g0 g1 := by
-- proof
  apply StatMech.Ising.lpMatchingFiveCurrentCoefficient_sum_nonpos_iff G beta J left right g0 g1 hg

/--
[lpGhostCurrentSquareGap_eq_emptyDisconn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpGhostCurrentSquareGap_eq_emptyDisconn_eq
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (hg : g0 ≠ g1) :
-- imply
  let T := lpMatchingGhostSource g0 g1 currentSum G beta J ∅ ^ 2 - currentSum G beta J T ^ 2 = sourcePairDisconnSum G beta J ∅ ∅ g0 g1 := by
-- proof
  apply StatMech.Ising.lpGhostCurrentSquareGap_eq_emptyDisconn G beta J g0 g1 hg

/--
[lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_centeredGram](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_centeredGram_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  ((∑ i : I, ∑ j : I, lpMatchingFiveCurrentCoefficient G beta J left right g0 g1 i j) <= 0) <-> lpMatchingDisconnCenteredGram G beta J left right g0 g1 <= 0 := by
-- proof
  apply StatMech.Ising.lpMatchingFiveCurrentCoefficient_sum_nonpos_iff_centeredGram G beta J left right g0 g1 hg

/--
[lpSourcePairDisconnSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpSourcePairDisconnSum_nonneg_eq
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {A B : Finset W}
  {u v : W}
-- given
  (J : Sym2 W -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e) :
-- imply
  0 <= sourcePairDisconnSum G beta J A B u v := by
-- proof
  apply StatMech.Ising.lpSourcePairDisconnSum_nonneg G beta J hbeta hJ A B u v

/--
[lpGhostCurrentSquareGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpGhostCurrentSquareGap_nonneg_eq
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (hg : g0 ≠ g1) :
-- imply
  let T := lpMatchingGhostSource g0 g1 0 <= currentSum G beta J ∅ ^ 2 - currentSum G beta J T ^ 2 := by
-- proof
  apply StatMech.Ising.lpGhostCurrentSquareGap_nonneg G beta J hbeta hJ g0 g1 hg

/--
[lpGhostSourceDisconn_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpGhostSourceDisconn_eq_zero_eq
  [DecidableEq W]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (hg : g0 ≠ g1) :
-- imply
  let T := lpMatchingGhostSource g0 g1 sourcePairDisconnSum G beta J T ∅ g0 g1 = 0 := by
-- proof
  apply StatMech.Ising.lpGhostSourceDisconn_eq_zero G beta J g0 g1 hg

/--
[lpMatchingDisconn_diagonal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingDisconn_diagonal_le_eq
  [DecidableEq W]
  [Fintype I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
  {i : I}
-- given
  (J : Sym2 W -> Real)
  (hbeta : 0 <= beta)
  (hJ : forall e, 0 <= J e)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  let Si := lpMatchingSeamSource left right i let T := lpMatchingGhostSource g0 g1 sourcePairDisconnSum G beta J ∅ ∅ g0 g1 * sourcePairDisconnSum G beta J (Si ∆ Si ∆ T) ∅ g0 g1 <= 2 * sourcePairDisconnSum G beta J Si ∅ g0 g1 * sourcePairDisconnSum G beta J (Si ∆ T) ∅ g0 g1 := by
-- proof
  apply StatMech.Ising.lpMatchingDisconn_diagonal_le G beta J hbeta hJ left right g0 g1 hg i

/--
[lpMatchingDisconnTwo_eq_offDiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterFiveCurrentPairing.lean)
-/
@[path]
private lemma lpMatchingDisconnTwo_eq_offDiag_eq
  [DecidableEq W]
  [Fintype I]
  [DecidableEq I]
  [Fintype W]
  {G : SimpleGraph W}
  [DecidableRel G.Adj]
  {beta : Real}
  {g0 g1 : W}
-- given
  (J : Sym2 W -> Real)
  (left right : I -> W)
  (hg : g0 ≠ g1) :
-- imply
  lpMatchingDisconnTwo G beta J left right g0 g1 = lpMatchingDisconnTwoOffDiag G beta J left right g0 g1 := by
-- proof
  apply StatMech.Ising.lpMatchingDisconnTwo_eq_offDiag G beta J left right g0 g1 hg


-- created on 2026-10-23
