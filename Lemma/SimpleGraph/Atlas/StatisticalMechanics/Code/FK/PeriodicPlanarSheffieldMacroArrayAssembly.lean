import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma exists_orbitBox_normalBoundaryBandFamily_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {N : Nat}
  {delta : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hdelta : 0 < delta) :
-- imply
  Nonempty (E.NormalBoundaryBandFamily mu (P.orbitBox N) ((mu.real (P.setHitsInfinite (P.orbitBox N : Set V))) ^ 2 - delta)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_orbitBox_normalBoundaryBandFamily E mu hFKG hTI hunique N hdelta

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma exists_alternatingMargins_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p} :
-- imply
  ∃ horizontal vertical : Nat → Nat, Tendsto horizontal atTop atTop ∧ Tendsto vertical atTop atTop ∧ (∀ n, (family.radiusLeft (horizontal n) : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusRight (horizontal n) : Int) + family.baseRight 1 ≤ family.baseBottom 1 + vertical n) ∧ (∀ n, (family.radiusBottom (vertical n) : Int) + family.baseBottom 0 ≤ family.baseLeft 0 + horizontal (n + 1)) ∧ (∀ n, (family.radiusTop (vertical n) : Int) + family.baseTop 0 ≤ family.baseLeft 0 + horizontal (n + 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.exists_alternatingMargins E family

/--
[PeriodicPlaneEmbedding.NormalBoundaryBandFamily.mixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma mixedBoundaryScores_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {p : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (horizontalMargin verticalMargin width height : Nat)
  (hfitLeft : (family.radiusLeft horizontalMargin : Int) + family.baseLeft 1 ≤ family.baseBottom 1 + verticalMargin)
  (hfitRight : (family.radiusRight horizontalMargin : Int) + family.baseRight 1 ≤ family.baseBottom 1 + verticalMargin) :
-- imply
  let gridBase : Site 2 := fun i ↦ if i = 0 then family.baseLeft 0 + horizontalMargin else family.baseBottom 1 + verticalMargin let b0 : Int := gridBase 0 + width - (family.baseRight 0 - horizontalMargin) let d1 : Int := gridBase 1 + height - (family.baseTop 1 - verticalMargin) let bottomLower : Int := gridBase 0 - family.baseBottom 0 - family.radiusBottom verticalMargin let topLower : Int := gridBase 0 - family.baseTop 0 - family.radiusTop verticalMargin let a1 : Int := min 0 (min bottomLower topLower) let bottomUpper : Int := gridBase 0 + width - family.baseBottom 0 + family.radiusBottom verticalMargin let topUpper : Int := gridBase 0 + width - family.baseTop 0 + family.radiusTop verticalMargin let b1 : Int := max b0 (max bottomUpper topUpper) let leftUpper : Int := gridBase 1 + height - family.baseLeft 1 + family.radiusLeft horizontalMargin let rightUpper : Int := gridBase 1 + height - family.baseRight 1 + family.radiusRight horizontalMargin let d0 : Int := max d1 (max leftUpper rightUpper) ((family.radiusLeft horizontalMargin : Int) ≤ b0) → ((family.radiusRight horizontalMargin : Int) ≤ b0) → ((family.radiusBottom verticalMargin : Int) ≤ d1) → ((family.radiusTop verticalMargin : Int) ≤ d1) → ((a1 : Real) ≤ 0 ∧ (b0 : Real) ≤ b1 ∧ (0 : Real) ≤ 0 ∧ (d1 : Real) ≤ d0) ∧ (∀ i : Fin (width + 1), p < mu.real (E.rectSideConnectionEvent a1 b1 0 d1 (P.shift (gridBase + preferenceGridSite (i, (0 : Fin (height + 1)))) '' (S : Set V)) (E.rectBottomBoundaryVertices a1 b1 0 d1))) ∧ (∀ i : Fin (width + 1), p < mu.real (E.rectSideConnectionEvent a1 b1 0 d1 (P.shift (gridBase + preferenceGridSite (i, Fin.last height)) '' (S : Set V)) (E.rectTopBoundaryVertices a1 b1 0 d1))) ∧ (∀ j : Fin (height + 1), p < mu.real (E.rectSideConnectionEvent 0 b0 0 d0 (P.shift (gridBase + preferenceGridSite ((0 : Fin (width + 1)), j)) '' (S : Set V)) (E.rectLeftBoundaryVertices 0 b0 0 d0))) ∧ (∀ j : Fin (height + 1), p < mu.real (E.rectSideConnectionEvent 0 b0 0 d0 (P.shift (gridBase + preferenceGridSite (Fin.last width, j)) '' (S : Set V)) (E.rectRightBoundaryVertices 0 b0 0 d0))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.NormalBoundaryBandFamily.mixedBoundaryScores E mu hTI family horizontalMargin verticalMargin width height hfitLeft hfitRight

/--
[PeriodicPlaneEmbedding.rectSideConnection_component_le_template](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma rectSideConnection_component_le_template_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {component template : Finset V}
  {base : Site 2}
  {side : Set V}
-- given
  (hcomponent : component ⊆ template) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (component.image (P.shift base) : Set V) side) ≤ mu.real (E.rectSideConnectionEvent a b c d (template.image (P.shift base) : Set V) side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnection_component_le_template E mu a b c d component template base side hcomponent

/--
[PeriodicPlaneEmbedding.rectSideConnection_leftComponent_le_fourShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma rectSideConnection_leftComponent_le_fourShift_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {S : Finset V}
  {zLeft zRight zBottom zTop base : Site 2}
  {side : Set V} :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d ((S.image (P.shift zLeft)).image (P.shift base) : Set V) side) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift base) : Set V) side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnection_leftComponent_le_fourShift E mu a b c d S zLeft zRight zBottom zTop base side

/--
[PeriodicPlaneEmbedding.rectSideConnection_rightComponent_le_fourShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma rectSideConnection_rightComponent_le_fourShift_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {S : Finset V}
  {zLeft zRight zBottom zTop base : Site 2}
  {side : Set V} :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d ((S.image (P.shift zRight)).image (P.shift base) : Set V) side) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift base) : Set V) side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnection_rightComponent_le_fourShift E mu a b c d S zLeft zRight zBottom zTop base side

/--
[PeriodicPlaneEmbedding.rectSideConnection_bottomComponent_le_fourShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma rectSideConnection_bottomComponent_le_fourShift_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {S : Finset V}
  {zLeft zRight zBottom zTop base : Site 2}
  {side : Set V} :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d ((S.image (P.shift zBottom)).image (P.shift base) : Set V) side) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift base) : Set V) side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnection_bottomComponent_le_fourShift E mu a b c d S zLeft zRight zBottom zTop base side

/--
[PeriodicPlaneEmbedding.rectSideConnection_topComponent_le_fourShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma rectSideConnection_topComponent_le_fourShift_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {a b c d : Real}
  {S : Finset V}
  {zLeft zRight zBottom zTop base : Site 2}
  {side : Set V} :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d ((S.image (P.shift zTop)).image (P.shift base) : Set V) side) ≤ mu.real (E.rectSideConnectionEvent a b c d ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift base) : Set V) side) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectSideConnection_topComponent_le_fourShift E mu a b c d S zLeft zRight zBottom zTop base side

/--
[PeriodicGraph.fourShiftTemplate_image_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma fourShiftTemplate_image_subset_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {S : Finset V}
  {zLeft zRight zBottom zTop base : Site 2}
  {R : Set V}
-- given
  (hleft : ((S.image (P.shift zLeft)).image (P.shift base) : Set V) ⊆ R)
  (hright : ((S.image (P.shift zRight)).image (P.shift base) : Set V) ⊆ R)
  (hbottom : ((S.image (P.shift zBottom)).image (P.shift base) : Set V) ⊆ R)
  (htop : ((S.image (P.shift zTop)).image (P.shift base) : Set V) ⊆ R) :
-- imply
  ((P.fourShiftTemplate S zLeft zRight zBottom zTop).image (P.shift base) : Set V) ⊆ R := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.fourShiftTemplate_image_subset P S zLeft zRight zBottom zTop base R hleft hright hbottom htop

/--
[boundaryGridBase_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma boundaryGridBase_add_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom z : Site 2} :
-- imply
  boundaryGridBase (baseLeft + z) (baseBottom + z) = boundaryGridBase baseLeft baseBottom + z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridBase_add baseLeft baseBottom z

/--
[boundaryGridWidth_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma boundaryGridWidth_add_eq
  [DecidableEq V]
  [Countable V]
  {extent : Nat}
  {baseLeft baseRight z : Site 2} :
-- imply
  boundaryGridWidth extent (baseLeft + z) (baseRight + z) = boundaryGridWidth extent baseLeft baseRight := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridWidth_add extent baseLeft baseRight z

/--
[boundaryGridHeight_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma boundaryGridHeight_add_eq
  [DecidableEq V]
  [Countable V]
  {extent : Nat}
  {baseBottom baseTop z : Site 2} :
-- imply
  boundaryGridHeight extent (baseBottom + z) (baseTop + z) = boundaryGridHeight extent baseBottom baseTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridHeight_add extent baseBottom baseTop z

/--
[PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.grid_subset_translated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma grid_subset_translated_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {radius : Nat → Nat}
  {data : E.ConnectorReadyCommonSquareData mu radius}
  {n extentX extentY : Nat}
  {z : Site 2}
-- given
  (hposX : 0 < data.baseRight n 0 + (extentX : Int) - data.baseLeft n 0)
  (hposY : 0 < data.baseTop n 1 + (extentY : Int) - data.baseBottom n 1) :
-- imply
  ∀ v : PreferenceGridVertex (boundaryGridWidth extentX (data.baseLeft n) (data.baseRight n)) (boundaryGridHeight extentY (data.baseBottom n) (data.baseTop n)), P.shift (boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V) ⊆ E.rectVertices (-(data.M n : Real) + z 0) ((data.M n + extentX : Nat) + (z 0 : Int)) (-(data.M n : Real) + z 1) ((data.M n + extentY : Nat) + (z 1 : Int)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.grid_subset_translated E data n extentX extentY z hposX hposY

/--
[PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.grid_subset_translated_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma grid_subset_translated_of_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {radius : Nat → Nat}
  {data : E.ConnectorReadyCommonSquareData mu radius}
  {n extentX extentY smallRadius : Nat}
  {z : Site 2}
-- given
  (hsmall : smallRadius ≤ radius n)
  (hposX : 0 < data.baseRight n 0 + (extentX : Int) - data.baseLeft n 0)
  (hposY : 0 < data.baseTop n 1 + (extentY : Int) - data.baseBottom n 1) :
-- imply
  ∀ v : PreferenceGridVertex (boundaryGridWidth extentX (data.baseLeft n) (data.baseRight n)) (boundaryGridHeight extentY (data.baseBottom n) (data.baseTop n)), P.shift (boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius smallRadius) : Set V) ⊆ E.rectVertices (-(data.M n : Real) + z 0) ((data.M n + extentX : Nat) + (z 0 : Int)) (-(data.M n : Real) + z 1) ((data.M n + extentY : Nat) + (z 1 : Int)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.grid_subset_translated_of_le E data n extentX extentY smallRadius z hsmall hposX hposY

/--
[PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.template_grid_subset_translated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldMacroArrayAssembly.lean)
-/
@[path]
private lemma template_grid_subset_translated_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {radius : Nat → Nat}
  {data : E.ConnectorReadyCommonSquareData mu radius}
  {n extentX extentY templateRadius : Nat}
  {z : Site 2}
-- given
  (htemplate : templateRadius ≤ radius n)
  (hposX : 0 < data.baseRight n 0 + (extentX : Int) - data.baseLeft n 0)
  (hposY : 0 < data.baseTop n 1 + (extentY : Int) - data.baseBottom n 1) :
-- imply
  ∀ v : PreferenceGridVertex (boundaryGridWidth extentX (data.baseLeft n) (data.baseRight n)) (boundaryGridHeight extentY (data.baseBottom n) (data.baseTop n)), P.shift (boundaryGridBase (data.baseLeft n + z) (data.baseBottom n + z) + preferenceGridSite v) '' (P.orbitBox templateRadius : Set V) ⊆ E.rectVertices (-(data.M n : Real) + z 0) ((data.M n + extentX : Nat) + (z 0 : Int)) (-(data.M n : Real) + z 1) ((data.M n + extentY : Nat) + (z 1 : Int)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.ConnectorReadyCommonSquareData.template_grid_subset_translated E data n extentX extentY templateRadius z htemplate hposX hposY


-- created on 2026-10-23
