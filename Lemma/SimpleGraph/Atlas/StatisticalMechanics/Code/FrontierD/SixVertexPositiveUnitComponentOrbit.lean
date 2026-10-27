import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPositiveUnitComponentOrbit.Part7
open Finset StatMech StatMech.FrontierD StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitCover


/--
[negativeComponents_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma negativeComponents_card_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {cardinality : Nat}
  {positive : BooleanLayer (SixVertexDisagreementComponent base.first base.second) cardinality} :
-- imply
  (base.negativeComponents positive).card = 2 * k - cardinality := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.negativeComponents_card base positive

/--
[mask_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma mask_full_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {cardinality : Nat}
  {positive : BooleanLayer (SixVertexDisagreementComponent base.first base.second) cardinality} :
-- imply
  SixVertexFullDisagreementMask base.first base.second (base.mask positive) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.mask_full base positive

/--
[mask_seamTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma mask_seamTransfer_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {cardinality : Nat}
  {positive : BooleanLayer (SixVertexDisagreementComponent base.first base.second) cardinality} :
-- imply
  sixVertexTorusMaskSeamTransfer (base.mask positive) base.first base.second = ((2 * k - cardinality : Nat) : Int) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.mask_seamTransfer base positive

/--
[mask_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma mask_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {cardinality : Nat} :
-- imply
  Function.Injective (base.mask (cardinality := cardinality)) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.mask_injective base

/--
[source_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma source_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  Function.Injective (fun positive => base.source positive hmiddle_pos hmiddle_lt) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.source_injective base hmiddle_pos hmiddle_lt

/--
[target_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma target_injective_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k} :
-- imply
  Function.Injective base.target := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.target_injective base

/--
[source_degreeTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma source_degreeTwo_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {positive : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  SixVertexLocallyDegreeTwo (base.source positive hmiddle_pos hmiddle_lt).1.1 (base.source positive hmiddle_pos hmiddle_lt).2.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.source_degreeTwo base positive hmiddle_pos hmiddle_lt

/--
[target_mask_eq_xor_of_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma target_mask_eq_xor_of_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {source : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {target : BooleanLayer (SixVertexDisagreementComponent base.first base.second) k}
-- given
  (hrelated : booleanMiddleLayerDownRelation source target) :
-- imply
  base.mask target = sixVertexTorusMaskXor (base.mask source) (sixVertexDisagreementComponentSetMask base.first base.second {booleanMiddleLayerAddedElement target source}) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.target_mask_eq_xor_of_related base source target hrelated

/--
[related_of_target_mask_eq_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma related_of_target_mask_eq_xor_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {source : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {target : BooleanLayer (SixVertexDisagreementComponent base.first base.second) k}
  {component : SixVertexDisagreementComponent base.first base.second}
-- given
  (hmasks : base.mask target = sixVertexTorusMaskXor (base.mask source) (sixVertexDisagreementComponentSetMask base.first base.second {component})) :
-- imply
  booleanMiddleLayerDownRelation source target := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.related_of_target_mask_eq_xor base source target component hmasks

/--
[componentRepresentativeEdge_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma componentRepresentativeEdge_disagrees_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {component : SixVertexDisagreementComponent base.first base.second} :
-- imply
  sixVertexTorusEdgeDisagrees base.first base.second (base.componentRepresentativeEdge component) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.componentRepresentativeEdge_disagrees base component

/--
[componentRepresentativeEdge_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma componentRepresentativeEdge_component_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {component : SixVertexDisagreementComponent base.first base.second} :
-- imply
  (sixVertexTorusDisagreementGraph base.first base.second).connectedComponentMk (base.componentRepresentativeEdge component) = component.1 := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.componentRepresentativeEdge_component base component

/--
[sourceComponentSeed_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma sourceComponentSeed_edge_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {positive : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {component : SixVertexDisagreementComponent base.first base.second}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  sixVertexDegreeTwoOrientedComponentEdge (base.source_degreeTwo positive hmiddle_pos hmiddle_lt) (base.sourceComponentSeed positive hmiddle_pos hmiddle_lt component) = base.componentRepresentativeEdge component := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.sourceComponentSeed_edge base positive hmiddle_pos hmiddle_lt component

/--
[sourceComponentSeed_strandMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma sourceComponentSeed_strandMask_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {positive : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {component : SixVertexDisagreementComponent base.first base.second}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (sixVertexDegreeTwoStrandDirectedSimpleCycle (base.source positive hmiddle_pos hmiddle_lt).1.2.1 (base.source positive hmiddle_pos hmiddle_lt).2.2.1 (base.source_degreeTwo positive hmiddle_pos hmiddle_lt) (base.sourceComponentSeed positive hmiddle_pos hmiddle_lt component)).mask = sixVertexDisagreementComponentSetMask base.first base.second {component} := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.sourceComponentSeed_strandMask base positive hmiddle_pos hmiddle_lt component

/--
[physicalRelated_of_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma physicalRelated_of_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {source : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {target : BooleanLayer (SixVertexDisagreementComponent base.first base.second) k}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hrelated : booleanMiddleLayerDownRelation source target) :
-- imply
  SixVertexDegreeTwoUnitStrandPhysicalRelated (base.sourceEmbedding hmiddle_pos hmiddle_lt source) (base.targetEmbedding target) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.physicalRelated_of_related base hmiddle_pos hmiddle_lt source target hrelated

/--
[related_of_physicalRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma related_of_physicalRelated_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {source : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {target : BooleanLayer (SixVertexDisagreementComponent base.first base.second) k}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hphysical : SixVertexDegreeTwoUnitStrandPhysicalRelated (base.sourceEmbedding hmiddle_pos hmiddle_lt source) (base.targetEmbedding target)) :
-- imply
  booleanMiddleLayerDownRelation source target := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.related_of_physicalRelated base hmiddle_pos hmiddle_lt source target hphysical

/--
[physicalRelated_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma physicalRelated_iff_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
  {source : BooleanLayer (SixVertexDisagreementComponent base.first base.second) (k + 1)}
  {target : BooleanLayer (SixVertexDisagreementComponent base.first base.second) k}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  SixVertexDegreeTwoUnitStrandPhysicalRelated (base.sourceEmbedding hmiddle_pos hmiddle_lt source) (base.targetEmbedding target) ↔ booleanMiddleLayerDownRelation source target := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.physicalRelated_iff base hmiddle_pos hmiddle_lt source target

/--
[hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma hall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {k : Nat}
  {base : SixVertexPositiveUnitComponentOrbitBase T middle k}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width) :
-- imply
  (base.presentation hmiddle_pos hmiddle_lt).Hall := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitBase.hall base hmiddle_pos hmiddle_lt

/--
[matching_related](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma matching_related_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentOrbitCover T middle hmiddle_pos hmiddle_lt Source}
  {source : Source} :
-- imply
  (cover.toAtlas).Related source (cover.matching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitCover.matching_related cover source

/--
[matching_fineRelated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma matching_fineRelated_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentOrbitCover T middle hmiddle_pos hmiddle_lt Source}
  {source : Source} :
-- imply
  sixVertexPairAtMostTwoCycleFineRelated ((cover.sourcePhysical source).1.1, (cover.sourcePhysical source).2.1) ((cover.matching source).1.1, (cover.matching source).2.1) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitCover.matching_fineRelated cover source

/--
[matching_layers_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma matching_layers_ne_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentOrbitCover T middle hmiddle_pos hmiddle_lt Source}
  {source : Source} :
-- imply
  (cover.matching source).1 ≠ (cover.matching source).2 := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitCover.matching_layers_ne cover source

/--
[matching_totalC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma matching_totalC_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentOrbitCover T middle hmiddle_pos hmiddle_lt Source}
  {source : Source} :
-- imply
  sixVertexConfigurationPairTotalCPhysical (cover.sourcePhysical source) = sixVertexConfigurationPairTotalCPhysical (cover.matching source) := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitCover.matching_totalC cover source

/--
[hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPositiveUnitComponentOrbit.lean)
-/
@[path]
private lemma hall_eq_2
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {cover : SixVertexPositiveUnitComponentOrbitCover T middle hmiddle_pos hmiddle_lt Source} :
-- imply
  ∀ sources : Finset Source, sources.card ≤ (Finset.univ.filter fun target : SixVertexConfigurationPhysicalTarget T middle => ∃ source ∈ sources, (cover.toAtlas).Related source target).card := by
-- proof
  apply StatMech.FrontierD.SixVertexPositiveUnitComponentOrbitCover.hall cover


-- created on 2026-10-23
