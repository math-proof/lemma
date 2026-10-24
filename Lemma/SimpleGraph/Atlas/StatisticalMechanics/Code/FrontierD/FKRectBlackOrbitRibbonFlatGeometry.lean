import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitRibbonFlatGeometry
open StatMech StatMech.FrontierD


/--
[fkRectList_get_flatMap_eight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectList_get_flatMap_eight_eq
  {α β : Type}
  {l : List α}
  {f : α → List β}
  {i : Fin l.length}
  {t : Fin 8}
-- given
  (hlen : ∀ a, (f a).length = 8) :
-- imply
  (l.flatMap f).get ⟨t.val + 8 * i.val, by rw [List.length_flatMap] simp [hlen] omega⟩ = (f (l.get i)).get ⟨t.val, by simpa [hlen] using t.isLt⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectList_get_flatMap_eight l f hlen i t

/--
[fkRectBlackOrbitMedialRibbonFlatDirection_eq_get](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonFlatDirection_eq_get_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length} :
-- imply
  fkRectBlackOrbitMedialRibbonFlatDirection R omega d k = (fkRectBlackOrbitMedialRibbonWord R omega d).get k := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonFlatDirection_eq_get R omega d k

/--
[finCongr_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma finCongr_add_one_eq
  {n m : ℕ}
  [NeZero n]
  [NeZero m]
  {k : Fin n}
-- given
  (h : n = m) :
-- imply
  finCongr h (k + 1) = finCongr h k + 1 := by
-- proof
  apply StatMech.FrontierD.finCongr_add_one h k

/--
[finProdFinEquiv_ribbonIndexSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma finProdFinEquiv_ribbonIndexSucc_eq
  {n : ℕ}
  [NeZero n]
  {z : Fin n × Fin 8}
-- given
  (hn : 0 < n) :
-- imply
  finProdFinEquiv (fkRectRibbonIndexSucc hn z) = finProdFinEquiv z + 1 := by
-- proof
  apply StatMech.FrontierD.finProdFinEquiv_ribbonIndexSucc hn z

/--
[fkRectBlackOrbitMedialRibbonIndexEquiv_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonIndexEquiv_add_one_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length} :
-- imply
  fkRectBlackOrbitMedialRibbonIndexEquiv R omega d (k + 1) = fkRectRibbonIndexSucc (fkRectBlackOrbitList_length_pos (fkRectConfigurationToMedialPairing R omega) d) (fkRectBlackOrbitMedialRibbonIndexEquiv R omega d k) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonIndexEquiv_add_one R omega d k

/--
[fkRectBlackOrbitMedialRibbonFlatSite_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonFlatSite_succ_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length} :
-- imply
  fkRectBlackOrbitMedialRibbonFlatSite R omega d (k + 1) = fkRectRibbonRectStep (8 * R.medialTorus.width) (8 * R.medialTorus.height) (fkRectBlackOrbitMedialRibbonFlatDirection R omega d k) (fkRectBlackOrbitMedialRibbonFlatSite R omega d k) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonFlatSite_succ R omega d k

/--
[fkRectRibbonRectStep_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectRibbonRectStep_opposite_eq
  {mu : Fin 4}
  {p : ZMod width × ZMod height}
-- given
  (width height : ℕ) :
-- imply
  fkRectRibbonRectStep width height (mu + 2) (fkRectRibbonRectStep width height mu p) = p := by
-- proof
  apply StatMech.FrontierD.fkRectRibbonRectStep_opposite width height mu p

/--
[fkRectBlackOrbitMedialRibbonWord_length_gt_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonWord_length_gt_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus} :
-- imply
  2 < (fkRectBlackOrbitMedialRibbonWord R omega d).length := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonWord_length_gt_two R omega d

/--
[fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBlackOrbitRibbonFlatGeometry.lean)
-/
@[path]
private lemma fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialBlackDart R.medialTorus}
  {k : Fin (fkRectBlackOrbitMedialRibbonWord R omega d).length} :
-- imply
  fkRectBlackOrbitMedialRibbonFlatDirection R omega d (k + 1) ≠ fkRectBlackOrbitMedialRibbonFlatDirection R omega d k + 2 := by
-- proof
  apply StatMech.FrontierD.fkRectBlackOrbitMedialRibbonFlatDirection_nonUturn R omega d k


-- created on 2026-10-23
