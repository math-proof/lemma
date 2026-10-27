import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectFaithfulVerticalRepeat
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectFaithfulShearDartRoute_translate_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulVerticalRepeat.lean)
-/
@[path]
private lemma fkRectFaithfulShearDartRoute_translate_fst_eq
  {t : Int × Int}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hr : r ∈ fkRectFaithfulShearDartRoute (fkRectIntegralSquareDartTranslate t d)) :
-- imply
  ∃ s ∈ fkRectFaithfulShearDartRoute d, r.1 = s.1 + 2 * (t.1 + t.2) := by
-- proof
  apply StatMech.FrontierD.fkRectFaithfulShearDartRoute_translate_fst t d r hr

/--
[fkRectRepeatTranslatedDartPath_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulVerticalRepeat.lean)
-/
@[path]
private lemma fkRectRepeatTranslatedDartPath_mem_eq
  {l : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat}
  {d : FKRectIntegralSquareDart}
-- given
  (hd : d ∈ fkRectRepeatTranslatedDartPath l u n) :
-- imply
  ∃ i : Nat, ∃ a ∈ l, d = fkRectIntegralSquareDartTranslate (fkRectNatScale i u) a := by
-- proof
  apply StatMech.FrontierD.fkRectRepeatTranslatedDartPath_mem l u n hd

/--
[fkRectRepeatTranslatedDartPath_faithfulRoute_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulVerticalRepeat.lean)
-/
@[path]
private lemma fkRectRepeatTranslatedDartPath_faithfulRoute_fst_bounds_eq
  {l : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat}
  {left right : Int}
  {d : FKRectIntegralSquareDart}
  {r : Int × Int}
-- given
  (hu : u.1 + u.2 = 0)
  (hbase : ∀ d ∈ l, ∀ r ∈ fkRectFaithfulShearDartRoute d, left ≤ r.1 ∧ r.1 ≤ right)
  (hd : d ∈ fkRectRepeatTranslatedDartPath l u n)
  (hr : r ∈ fkRectFaithfulShearDartRoute d) :
-- imply
  left ≤ r.1 ∧ r.1 ≤ right := by
-- proof
  apply StatMech.FrontierD.fkRectRepeatTranslatedDartPath_faithfulRoute_fst_bounds l u n hu left right hbase hd hr

/--
[fkRectRepeatTranslatedDartPath_ne_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulVerticalRepeat.lean)
-/
@[path]
private lemma fkRectRepeatTranslatedDartPath_ne_nil_eq
  {l : List FKRectIntegralSquareDart}
  {u : Int × Int}
  {n : Nat}
-- given
  (hl : l ≠ [])
  (hn : 0 < n) :
-- imply
  fkRectRepeatTranslatedDartPath l u n ≠ [] := by
-- proof
  apply StatMech.FrontierD.fkRectRepeatTranslatedDartPath_ne_nil l u n hl hn

/--
[exists_fkRectFaithfulRepeatedVerticalWalk_fst_bounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectFaithfulVerticalRepeat.lean)
-/
@[path]
private lemma exists_fkRectFaithfulRepeatedVerticalWalk_fst_bounds_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {x : R.Vertex}
  {w : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x x}
  {p q : Int × Int}
  {l : List FKRectIntegralSquareDart}
  {right : Nat}
  {n : Nat}
-- given
  (halong : FKRectRefinedOpenWalkBlocksAlong R F w p q l)
  (hpath : FKRectIntegralSquareDartPath (fkRectRefinedScalePoint (fkRectSquareDevelopPoint p)) (fkRectRefinedScalePoint (fkRectSquareDevelopPoint q)) l)
  (hl : l ≠ [])
  (hsupport : ∀ v ∈ w.support, 1 ≤ v.1.val ∧ v.1.val ≤ right)
  (hpcol : p.1 = (x.1.val : Int))
  (hw : fkRectWalkWinding R w = (0, 1))
  (hn : 0 < n) :
-- imply
  let P := fkRectRefinedScalePoint (fkRectSquareDevelopPoint p) ∃ V : (hypercubicLattice 2).Walk (fkRectFaithfulShearPoint P) ![(fkRectFaithfulShearPoint P) 0, (fkRectFaithfulShearPoint P) 1 + (n : Int) * (8 * (R.height : Int))], ∀ z ∈ V.support, 16 ≤ z 0 ∧ z 0 ≤ 16 * (right : Int) + 8 := by
-- proof
  apply StatMech.FrontierD.exists_fkRectFaithfulRepeatedVerticalWalk_fst_bounds R F halong hpath hl right hsupport hpcol hw n hn


-- created on 2026-10-23
