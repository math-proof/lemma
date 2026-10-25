import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[card_fkRectRawHorizontalCrossingSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma card_fkRectRawHorizontalCrossingSource_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  Fintype.card {y : Fin R.height // FKRectRawHorizontalCrossingSource R eta y} = fkRectRawHorizontalCrossingSourceCount R eta := by
-- proof
  apply StatMech.FrontierD.card_fkRectRawHorizontalCrossingSource R eta

/--
[fkRectRawHorizontalCrossingSourceCount_le_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingSourceCount_le_height_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectRawHorizontalCrossingSourceCount R eta ≤ R.height := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingSourceCount_le_height R eta

/--
[fkRectRawHorizontalCrossingClusterCount_le_sourceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingClusterCount_le_sourceCount_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectRawHorizontalCrossingClusterCount R eta ≤ fkRectRawHorizontalCrossingSourceCount R eta := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingClusterCount_le_sourceCount R eta

/--
[fkRectRawHorizontalCrossingClusterCount_le_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingClusterCount_le_height_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectRawHorizontalCrossingClusterCount R eta ≤ R.height := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingClusterCount_le_height R eta

/--
[fkRectRawHorizontalCrossingRepresentative_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingRepresentative_component_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {C : {C : (fkRectOpenGraph R eta).ConnectedComponent // FKRectRawHorizontalCrossingComponent R eta C}} :
-- imply
  (fkRectOpenGraph R eta).connectedComponentMk (fkRectLeftColumn R, fkRectRawHorizontalCrossingRepresentative R eta C) = C.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingRepresentative_component R eta C

/--
[fkRectRawHorizontalCrossingRepresentative_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingRepresentative_source_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {C : {C : (fkRectOpenGraph R eta).ConnectedComponent // FKRectRawHorizontalCrossingComponent R eta C}} :
-- imply
  FKRectRawHorizontalCrossingSource R eta (fkRectRawHorizontalCrossingRepresentative R eta C) := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingRepresentative_source R eta C

/--
[fkRectRawHorizontalCrossingRepresentative_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingRepresentative_injective_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  Function.Injective (fkRectRawHorizontalCrossingRepresentative R eta) := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingRepresentative_injective R eta

/--
[card_fkRectRawHorizontalCrossingRepresentativeIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma card_fkRectRawHorizontalCrossingRepresentativeIndices_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  (fkRectRawHorizontalCrossingRepresentativeIndices R eta).card = fkRectRawHorizontalCrossingClusterCount R eta := by
-- proof
  apply StatMech.FrontierD.card_fkRectRawHorizontalCrossingRepresentativeIndices R eta

/--
[fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  ∀ i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta, FKRectRawHorizontalCrossingSource R eta i := by
-- proof
  apply StatMech.FrontierD.fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources R eta

/--
[eq_of_representativeIndices_of_component_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma eq_of_representativeIndices_of_component_eq_eq
  {R : FKRectTorus}
  {eta : R.Configuration}
  {i j : Fin R.height}
-- given
  (hi : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta)
  (hj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R eta)
  (hcomponent : (fkRectOpenGraph R eta).connectedComponentMk (fkRectLeftColumn R, i) = (fkRectOpenGraph R eta).connectedComponentMk (fkRectLeftColumn R, j)) :
-- imply
  i = j := by
-- proof
  apply StatMech.FrontierD.eq_of_representativeIndices_of_component_eq R eta hi hj hcomponent

/--
[fkRectCutHorizontalCrossingClusterCount_eq_raw](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectCutHorizontalCrossingClusterCount_eq_raw_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectCutHorizontalCrossingClusterCount R omega = fkRectRawHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectCutHorizontalCrossingClusterCount_eq_raw R omega

/--
[fkRectPrimalDualHorizontalCrossingClusterCount_forceCutClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectPrimalDualHorizontalCrossingClusterCount_forceCutClosed_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  fkRectPrimalDualHorizontalCrossingClusterCount R (fkRectForceCutClosed R omega) = fkRectPrimalDualHorizontalCrossingClusterCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalDualHorizontalCrossingClusterCount_forceCutClosed R omega

/--
[card_fkRectPrimalDualCrossingSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma card_fkRectPrimalDualCrossingSource_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  Fintype.card {i : Fin (2 * R.height) // FKRectPrimalDualCrossingSource R eta i} = fkRectRawHorizontalCrossingSourceCount R (fkRectForceCutClosed R eta) + fkRectRawHorizontalCrossingSourceCount R (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R eta)) := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalDualCrossingSource R eta

/--
[fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectRawPrimalDualHorizontalCrossingClusterCount R eta <= fkRectRawHorizontalCrossingSourceCount R eta + fkRectRawHorizontalCrossingSourceCount R (fkRectDualConfigurationEquiv R eta) := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalDualHorizontalCrossingClusterCount_le_sourceCount R eta

/--
[fkRectPrimalDualHorizontalCrossingClusterCount_le_sourceCount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectPrimalDualHorizontalCrossingClusterCount_le_sourceCount_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectPrimalDualHorizontalCrossingClusterCount R eta <= fkRectRawHorizontalCrossingSourceCount R (fkRectForceCutClosed R eta) + fkRectRawHorizontalCrossingSourceCount R (fkRectDualConfigurationEquiv R (fkRectForceCutClosed R eta)) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalDualHorizontalCrossingClusterCount_le_sourceCount R eta

/--
[fkRectPrimalDualCrossingRepresentativeSourceIndex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectPrimalDualCrossingRepresentativeSourceIndex_injective_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  Function.Injective (fkRectPrimalDualCrossingRepresentativeSourceIndex R eta) := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalDualCrossingRepresentativeSourceIndex_injective R eta

/--
[card_fkRectPrimalDualCrossingRepresentativeSourceIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma card_fkRectPrimalDualCrossingRepresentativeSourceIndices_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  (fkRectPrimalDualCrossingRepresentativeSourceIndices R eta).card = fkRectPrimalDualHorizontalCrossingClusterCount R eta := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalDualCrossingRepresentativeSourceIndices R eta

/--
[fkRectPrimalDualCrossingRepresentativeSourceIndices_subset_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectPrimalDualCrossingRepresentativeSourceIndices_subset_sources_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  ∀ i ∈ fkRectPrimalDualCrossingRepresentativeSourceIndices R eta, FKRectPrimalDualCrossingSource R eta i := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalDualCrossingRepresentativeSourceIndices_subset_sources R eta

/--
[fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectRawPrimalDualHorizontalCrossingClusterCount R eta ≤ 2 * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectRawPrimalDualHorizontalCrossingClusterCount_le_two_height R eta

/--
[fkRectPrimalDualHorizontalCrossingClusterCount_le_two_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalDualCrossings.lean)
-/
@[path]
private lemma fkRectPrimalDualHorizontalCrossingClusterCount_le_two_height_eq
  {R : FKRectTorus}
  {eta : R.Configuration} :
-- imply
  fkRectPrimalDualHorizontalCrossingClusterCount R eta <= 2 * R.height := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalDualHorizontalCrossingClusterCount_le_two_height R eta


-- created on 2026-10-23
