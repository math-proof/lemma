import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
open SimpleGraph Function StatMech StatMech.Walls


/--
[jc4_tnp_footprintAgree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_tnp_footprintAgree_eq
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc3_AvoidsEarFootprint r e) :
-- imply
  bpc_NotProbed r e := by
-- proof
  apply StatMech.Walls.jc4_tnp_footprintAgree r e h

/--
[jc4_tail_notProbed_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_tail_notProbed_single_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {m i : ℕ}
-- given
  (h : jc3_AvoidsEarFootprint r ((dartNext K)^[m + i] a.1)) :
-- imply
  bpc_NotProbed r ((dartNext K)^[m + i] a.1) := by
-- proof
  apply StatMech.Walls.jc4_tail_notProbed_single K a r m i h

/--
[jc4_tail_notProbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_tail_notProbed_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {m n : ℕ}
-- given
  (h : jc4_TailFootprintFree K a r m n) :
-- imply
  ∀ i, i < n → bpc_NotProbed r ((dartNext K)^[m + i] a.1) := by
-- proof
  apply StatMech.Walls.jc4_tail_notProbed K a r m n h

/--
[jc4_tailFootprintFree_of_vacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_tailFootprintFree_of_vacuous_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {m : ℕ} :
-- imply
  jc4_TailFootprintFree K a r m 0 := by
-- proof
  apply StatMech.Walls.jc4_tailFootprintFree_of_vacuous K a r m

/--
[jc4_farTail_footprintFree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_farTail_footprintFree_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {m n : ℕ}
-- given
  (hconst : ∀ i, i < n → (dartNext K)^[m + i] a.1 = jc3_farDart) :
-- imply
  jc4_TailFootprintFree K a (![0, 0] : Site 2) m n := by
-- proof
  apply StatMech.Walls.jc4_farTail_footprintFree K a m n hconst

/--
[jc4_farTail_notProbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_farTail_notProbed_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {m n : ℕ}
-- given
  (hconst : ∀ i, i < n → (dartNext K)^[m + i] a.1 = jc3_farDart) :
-- imply
  ∀ i, i < n → bpc_NotProbed (![0, 0] : Site 2) ((dartNext K)^[m + i] a.1) := by
-- proof
  apply StatMech.Walls.jc4_farTail_notProbed K a m n hconst

/--
[jc4_spliceTailClause](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_spliceTailClause_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' n : ℕ}
-- given
  (heq : ∀ i, i < n → (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1)
  (hconf : jc4_TailFootprintFree K a r m n) :
-- imply
  ∀ i, i < n → (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1 ∧ bpc_NotProbed r ((dartNext K)^[m + i] a.1) := by
-- proof
  apply StatMech.Walls.jc4_spliceTailClause K a r a' m m' n heq hconf

/--
[jc4_orbitSpliceDatum_of_confined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc4_tailnotprobed.lean)
-/
@[path]
private lemma jc4_orbitSpliceDatum_of_confined_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {a' : {e : Dart // IsBoundaryDart (K \ {r}) e}}
  {m m' n : ℕ}
-- given
  (hne' : (K \ {r}).Nonempty)
  (hp : dartOrbitPeriod K a = m + n)
  (hp' : dartOrbitPeriod (K \ {r}) a' = m' + n)
  (heq : ∀ i, i < n → (dartNext (K \ {r}))^[m' + i] a'.1 = (dartNext K)^[m + i] a.1)
  (hconf : jc4_TailFootprintFree K a r m n)
  (hbal : jc_windowTurn (K \ {r}) a'.1 0 m' = jc_windowTurn K a.1 0 m) :
-- imply
  jc3_OrbitSpliceDatum K a r := by
-- proof
  apply StatMech.Walls.jc4_orbitSpliceDatum_of_confined K a r hne' a' m m' n hp hp' heq hconf hbal


-- created on 2026-10-23
