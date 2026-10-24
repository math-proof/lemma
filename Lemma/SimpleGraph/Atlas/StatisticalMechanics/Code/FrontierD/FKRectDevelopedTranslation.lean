import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDevelopedTranslation
open Set StatMech StatMech.FrontierD


/--
[fkRectCriticalEventMass_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hs : Even s) :
-- imply
  fkRectCriticalEventMass R q A = fkRectCriticalEventMass R q ((fkRectEvenRowTranslationConfigurationEquiv R s) '' A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_evenRowTranslation R s hs q A

/--
[fkRectTorusGraph_adj_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {x y : R.Vertex} :
-- imply
  (fkRectTorusGraph R).Adj (fkRectColumnTranslationVertexEquiv R s x) (fkRectColumnTranslationVertexEquiv R s y) ↔ (fkRectTorusGraph R).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_columnTranslation R s x y

/--
[fkRectFullGraphConfiguration_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {omega : R.Configuration}
  {e : Sym2 R.Vertex} :
-- imply
  fkRectFullGraphConfiguration R (fkRectColumnTranslationConfigurationEquiv R s omega) (Sym2.map (fkRectColumnTranslationVertexEquiv R s) e) = fkRectFullGraphConfiguration R omega e := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_columnTranslation R s omega e

/--
[fkRectFullGraphConfiguration_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {omega : R.Configuration}
  {e : Sym2 R.Vertex}
-- given
  (hs : Even s) :
-- imply
  fkRectFullGraphConfiguration R (fkRectEvenRowTranslationConfigurationEquiv R s omega) (Sym2.map (fkRectEvenRowTranslationVertexEquiv R s) e) = fkRectFullGraphConfiguration R omega e := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_evenRowTranslation R s hs omega e

/--
[fkRectDevelopedSiteTranslate_apply_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectDevelopedSiteTranslate_apply_zero_eq
  {u : Int × Int}
  {z : Site 2} :
-- imply
  fkRectDevelopedSiteTranslate u z 0 = z 0 + u.1 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSiteTranslate_apply_zero u z

/--
[fkRectDevelopedSiteTranslate_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectDevelopedSiteTranslate_apply_one_eq
  {u : Int × Int}
  {z : Site 2} :
-- imply
  fkRectDevelopedSiteTranslate u z 1 = z 1 + u.2 := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSiteTranslate_apply_one u z

/--
[fkRectSquareUndevelopPoint_add_checkerboardTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectSquareUndevelopPoint_add_checkerboardTranslation_eq
  {z : Int × Int}
  {c t : Int} :
-- imply
  fkRectSquareUndevelopPoint (z + (c + t, c - t)) = fkRectSquareUndevelopPoint z + (c, 2 * t) := by
-- proof
  apply StatMech.FrontierD.fkRectSquareUndevelopPoint_add_checkerboardTranslation z c t

/--
[fkRectIntModFin_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectIntModFin_add_eq
  {N : Nat}
  {z s : Int}
-- given
  (hN : 0 < N) :
-- imply
  fkRectIntModFin hN (((fkRectIntModFin hN z).val : Int) + s) = fkRectIntModFin hN (z + s) := by
-- proof
  apply StatMech.FrontierD.fkRectIntModFin_add hN z s

/--
[fkRectColumnTranslation_squareRepresentativeVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslation_squareRepresentativeVertex_eq
  {R : FKRectTorus}
  {c : Int}
  {z : Int × Int} :
-- imply
  fkRectColumnTranslationVertexEquiv R c (fkRectSquareRepresentativeVertex R z) = fkRectSquareRepresentativeVertex R (z + (c, c)) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslation_squareRepresentativeVertex R c z

/--
[fkRectEvenRowTranslation_squareRepresentativeVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslation_squareRepresentativeVertex_eq
  {R : FKRectTorus}
  {t : Nat} :
-- imply
  Even (2 * t) → ∀ z : Int × Int, fkRectEvenRowTranslationVertexEquiv R (2 * t) (fkRectSquareRepresentativeVertex R z) = fkRectSquareRepresentativeVertex R (z + ((t : Int), -(t : Int))) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslation_squareRepresentativeVertex R t

/--
[fkRectCheckerboardTranslationVertexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCheckerboardTranslationVertexEquiv_apply_eq
  {R : FKRectTorus}
  {c : Int}
  {t : Nat}
  {v : R.Vertex} :
-- imply
  fkRectCheckerboardTranslationVertexEquiv R c t v = fkRectColumnTranslationVertexEquiv R c (fkRectEvenRowTranslationVertexEquiv R (2 * t) v) := by
-- proof
  apply StatMech.FrontierD.fkRectCheckerboardTranslationVertexEquiv_apply R c t v

/--
[fkRectCheckerboardTranslationConfigurationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCheckerboardTranslationConfigurationEquiv_apply_eq
  {R : FKRectTorus}
  {c : Int}
  {t : Nat}
  {omega : R.Configuration} :
-- imply
  fkRectCheckerboardTranslationConfigurationEquiv R c t omega = fkRectColumnTranslationConfigurationEquiv R c (fkRectEvenRowTranslationConfigurationEquiv R (2 * t) omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCheckerboardTranslationConfigurationEquiv_apply R c t omega

/--
[fkRectCheckerboardTranslation_squareRepresentativeVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCheckerboardTranslation_squareRepresentativeVertex_eq
  {R : FKRectTorus}
  {c : Int}
  {t : Nat}
  {z : Int × Int} :
-- imply
  fkRectCheckerboardTranslationVertexEquiv R c t (fkRectSquareRepresentativeVertex R z) = fkRectSquareRepresentativeVertex R (z + (c + t, c - t)) := by
-- proof
  apply StatMech.FrontierD.fkRectCheckerboardTranslation_squareRepresentativeVertex R c t z

/--
[fkRectFullGraphConfiguration_checkerboardTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectFullGraphConfiguration_checkerboardTranslation_eq
  {R : FKRectTorus}
  {c : Int}
  {t : Nat}
  {omega : R.Configuration}
  {e : Sym2 R.Vertex} :
-- imply
  fkRectFullGraphConfiguration R (fkRectCheckerboardTranslationConfigurationEquiv R c t omega) (Sym2.map (fkRectCheckerboardTranslationVertexEquiv R c t) e) = fkRectFullGraphConfiguration R omega e := by
-- proof
  apply StatMech.FrontierD.fkRectFullGraphConfiguration_checkerboardTranslation R c t omega e

/--
[fkRectCriticalRandomClusterProb_checkerboardTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_checkerboardTranslation_eq
  {R : FKRectTorus}
  {c : Int}
  {t : Nat}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectCriticalRandomClusterProb R q (fkRectCheckerboardTranslationConfigurationEquiv R c t omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_checkerboardTranslation R c t q omega

/--
[fkRectCriticalEventMass_checkerboardTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_checkerboardTranslation_eq
  {R : FKRectTorus}
  {c : Int}
  {t : Nat}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q A = fkRectCriticalEventMass R q ((fkRectCheckerboardTranslationConfigurationEquiv R c t) '' A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_checkerboardTranslation R c t q A

/--
[fkRectCheckerboardTranslation_developedSquareVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCheckerboardTranslation_developedSquareVertex_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {z : Site 2} :
-- imply
  fkRectCheckerboardTranslationVertexEquiv R c t (fkRectDevelopedSquareVertex R n z) = fkRectDevelopedSquareVertex R n (fkRectDevelopedSiteTranslate (c + t, c - t) z) := by
-- proof
  apply StatMech.FrontierD.fkRectCheckerboardTranslation_developedSquareVertex R n c t z

/--
[fkRectDevelopedSquarePullback_checkerboardTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectDevelopedSquarePullback_checkerboardTranslation_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {omega : R.Configuration}
  {e : Sym2 (Site 2)} :
-- imply
  fkRectDevelopedSquarePullback R n (fkRectCheckerboardTranslationConfigurationEquiv R c t omega) (Sym2.map (fkRectDevelopedSiteTranslate (c + t, c - t)) e) = fkRectDevelopedSquarePullback R n omega e := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquarePullback_checkerboardTranslation R n c t omega e

/--
[fkRectDevelopedSquarePullback_translateConfig_checkerboardTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectDevelopedSquarePullback_translateConfig_checkerboardTranslation_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {omega : R.Configuration} :
-- imply
  StatMech.Universality.translateConfig (![c + t, c - t] : Site 2) (fkRectDevelopedSquarePullback R n (fkRectCheckerboardTranslationConfigurationEquiv R c t omega)) = fkRectDevelopedSquarePullback R n omega := by
-- proof
  apply StatMech.FrontierD.fkRectDevelopedSquarePullback_translateConfig_checkerboardTranslation R n c t omega

/--
[fkRectCheckerboardTranslation_mem_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCheckerboardTranslation_mem_horizontalCrossing_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {a b d e : Int}
  {omega : R.Configuration}
-- given
  (hcross : omega ∈ fkRectDevelopedRectangleHorizontalCrossingEvent R n a b d e) :
-- imply
  fkRectCheckerboardTranslationConfigurationEquiv R c t omega ∈ fkRectDevelopedRectangleHorizontalCrossingEvent R n (a + (c + t)) (b + (c + t)) (d + (c - t)) (e + (c - t)) := by
-- proof
  apply StatMech.FrontierD.fkRectCheckerboardTranslation_mem_horizontalCrossing R n c t a b d e omega hcross

/--
[fkRectCheckerboardTranslation_mem_verticalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCheckerboardTranslation_mem_verticalCrossing_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {a b d e : Int}
  {omega : R.Configuration}
-- given
  (hcross : omega ∈ fkRectDevelopedRectangleVerticalCrossingEvent R n a b d e) :
-- imply
  fkRectCheckerboardTranslationConfigurationEquiv R c t omega ∈ fkRectDevelopedRectangleVerticalCrossingEvent R n (a + (c + t)) (b + (c + t)) (d + (c - t)) (e + (c - t)) := by
-- proof
  apply StatMech.FrontierD.fkRectCheckerboardTranslation_mem_verticalCrossing R n c t a b d e omega hcross

/--
[fkRectCritical_horizontalCrossingMass_le_checkerboardTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCritical_horizontalCrossingMass_le_checkerboardTranslate_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {q : Real}
  {a b d e : Int}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n a b d e) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n (a + (c + t)) (b + (c + t)) (d + (c - t)) (e + (c - t))) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_horizontalCrossingMass_le_checkerboardTranslate R n c t hq a b d e

/--
[fkRectCritical_verticalCrossingMass_le_checkerboardTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCritical_verticalCrossingMass_le_checkerboardTranslate_eq
  {R : FKRectTorus}
  {n : Nat}
  {c : Int}
  {t : Nat}
  {q : Real}
  {a b d e : Int}
-- given
  (hq : 0 < q) :
-- imply
  fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n a b d e) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n (a + (c + t)) (b + (c + t)) (d + (c - t)) (e + (c - t))) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_verticalCrossingMass_le_checkerboardTranslate R n c t hq a b d e

/--
[fkRectCritical_developedSquareHorizontalMass_ge_evenTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareHorizontalMass_ge_evenTranslate_eq
  {R : FKRectTorus}
  {n shift : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleHorizontalCrossingEvent R n (2 * shift) (2 * shift + n) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareHorizontalMass_ge_evenTranslate R n shift hn hwidth hheight hq

/--
[fkRectCritical_developedSquareVerticalMass_ge_evenTranslate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDevelopedTranslation.lean)
-/
@[path]
private lemma fkRectCritical_developedSquareVerticalMass_ge_evenTranslate_eq
  {R : FKRectTorus}
  {n shift : Nat}
  {q : Real}
-- given
  (hn : 1 ≤ n)
  (hwidth : 3 * n < R.width)
  (hheight : 3 * n < R.height)
  (hq : 1 ≤ q) :
-- imply
  1 / (2 * (1 + q)) ≤ fkRectCriticalEventMass R q (fkRectDevelopedRectangleVerticalCrossingEvent R n (2 * shift) (2 * shift + n) 0 n) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_developedSquareVerticalMass_ge_evenTranslate R n shift hn hwidth hheight hq


-- created on 2026-10-23
