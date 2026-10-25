import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc4_core.Part3
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc4_align_lockstep_bdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_align_lockstep_bdd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' : ℕ}
  {i : ℕ}
-- given
  (hmerge : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
  (hconf : ∀ j, j < i → jc3_AvoidsEarFootprint r ((dartNext K)^[m + j] a.1)) :
-- imply
  (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 := by
-- proof
  apply StatMech.Walls.jc4_align_lockstep_bdd K a r a' m m' hmerge i hconf

/--
[jc4_align_lockstep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_align_lockstep_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' : ℕ}
  {i : ℕ}
-- given
  (hmerge : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
  (hconf : ∀ j, jc3_AvoidsEarFootprint r ((dartNext K)^[m + j] a.1)) :
-- imply
  (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 := by
-- proof
  apply StatMech.Walls.jc4_align_lockstep K a r a' m m' hmerge hconf i

/--
[jc4_mergeDatum_of_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_mergeDatum_of_reaches_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' n : ℕ}
-- given
  (hne' : (K \ {r}).Nonempty)
  (hp : dartOrbitPeriod K a = m + n)
  (hp' : dartOrbitPeriod (K \ {r}) a' = m' + n)
  (hreach : (dartNext (K \ {r}))^[m'] a'.1 = (dartNext K)^[m] a.1)
  (hconf : ∀ i, i < n → jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1))
  (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m) :
-- imply
  jc4_MergeDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_mergeDatum_of_reaches K a r hne' a' m m' n hp hp' hreach hconf hbal

/--
[jc4_splice_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_splice_of_merge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (h : jc4_MergeDatum K a r) :
-- imply
  jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_splice_of_merge K a r h

/--
[jc4_merge_strengthens_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_merge_strengthens_splice_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2} :
-- imply
  jc4_MergeDatum K a r → jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_merge_strengthens_splice K a r

/--
[jc4_saturatingOrbitSplice_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_saturatingOrbitSplice_of_merge_eq
-- given
  (h : jc4_SaturatingMerge) :
-- imply
  jc3_SaturatingOrbitSplice := by
-- proof
  apply StatMech.Walls.jc4_saturatingOrbitSplice_of_merge h

/--
[jc4_saturatingEarMatch_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_saturatingEarMatch_of_merge_eq
-- given
  (h : jc4_SaturatingMerge) :
-- imply
  jc2_SaturatingEarMatch := by
-- proof
  apply StatMech.Walls.jc4_saturatingEarMatch_of_merge h

/--
[jc4_balanceSaturatingContraction_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_balanceSaturatingContraction_of_merge_eq
-- given
  (h : jc4_SaturatingMerge) :
-- imply
  bpc_BalanceSaturatingContraction := by
-- proof
  apply StatMech.Walls.jc4_balanceSaturatingContraction_of_merge h

/--
[jc4_balancePreservingContraction_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_balancePreservingContraction_of_merge_eq
-- given
  (h : jc4_SaturatingMerge) :
-- imply
  BalancePreservingContraction := by
-- proof
  apply StatMech.Walls.jc4_balancePreservingContraction_of_merge h

/--
[jc4_starHull_totalTurn_eq_four_of_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_starHull_totalTurn_eq_four_of_merge_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart (ndt_StarHull K) e}}
-- given
  (h : jc4_SaturatingMerge)
  (hSK : (ndt_StarHull K).Finite)
  (hne : (ndt_StarHull K).Nonempty) :
-- imply
  totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = 4 ∨ totalTurnZ (ndt_StarHull K) a.1 (dartOrbitPeriod (ndt_StarHull K) a) = -4 := by
-- proof
  apply StatMech.Walls.jc4_starHull_totalTurn_eq_four_of_merge h K hSK hne a

/--
[jc4_degenerate_mergeDatum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_degenerate_mergeDatum_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1))
  (hne : r ≠ a.1.tail)
  (hne' : (K \ {r}).Nonempty) :
-- imply
  jc4_MergeDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_degenerate_mergeDatum K a r hfoot hne hne'

/--
[jc4_farCell_mergeDatum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_farCell_mergeDatum_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1))
  (hr : r ∉ bpc_orbitFootprint K a)
  (hne' : (K \ {r}).Nonempty) :
-- imply
  jc4_MergeDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_farCell_mergeDatum K a r hfoot hr hne'

/--
[jc4_degenerate_merge_gives_splice](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_core.lean)
-/
@[path]
private lemma jc4_degenerate_merge_gives_splice_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc3_AvoidsEarFootprint r ((dartNext K)^[i] a.1))
  (hne : r ≠ a.1.tail)
  (hne' : (K \ {r}).Nonempty) :
-- imply
  jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_degenerate_merge_gives_splice K a r hfoot hne hne'


-- created on 2026-10-23
