import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalProfileReflection.Part9
open Finset StatMech StatMech.FrontierD


/--
[sixVertexCyclicNeg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexCyclicNeg_zero_eq
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexCyclicNeg hN (⟨0, hN⟩ : Fin N) = ⟨0, hN⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicNeg_zero hN

/--
[sixVertexCyclicNeg_val_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexCyclicNeg_val_of_ne_zero_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N)
  (hi : i.val ≠ 0) :
-- imply
  (sixVertexCyclicNeg hN i).val = N - i.val := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicNeg_val_of_ne_zero hN i hi

/--
[sixVertexCyclicNeg_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexCyclicNeg_involutive_eq
  {N : Nat}
-- given
  (hN : 0 < N) :
-- imply
  Function.Involutive (sixVertexCyclicNeg hN) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicNeg_involutive hN

/--
[sixVertexCyclicNeg_even_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexCyclicNeg_even_iff_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N)
  (hEven : Even N) :
-- imply
  Even (sixVertexCyclicNeg hN i).val ↔ Even i.val := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicNeg_even_iff hN hEven i

/--
[sixVertexCyclicNeg_cyclicPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexCyclicNeg_cyclicPred_eq
  {N : Nat}
  {i : Fin N}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexCyclicNeg hN (SixVertexArrows.cyclicPred hN i) = finitePeriodicSucc hN (sixVertexCyclicNeg hN i) := by
-- proof
  apply StatMech.FrontierD.sixVertexCyclicNeg_cyclicPred hN i

/--
[fkMedialVertexParity_cyclicNeg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma fkMedialVertexParity_cyclicNeg_eq
  {T : EvenTorus}
  {v : T.Vertex} :
-- imply
  fkMedialVertexParity (sixVertexCyclicNeg T.width_pos v.1, v.2) = fkMedialVertexParity v := by
-- proof
  apply StatMech.FrontierD.fkMedialVertexParity_cyclicNeg v

/--
[sixVertexHorizontalGaugeBit_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalGaugeBit_reflect_eq
  {T : EvenTorus}
  {v : T.Vertex}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalGaugeBit (sixVertexReflectHorizontalField horizontal) v = sixVertexHorizontalGaugeBit horizontal (sixVertexCyclicNeg T.width_pos v.1, v.2) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalGaugeBit_reflect horizontal v

/--
[sixVertexHorizontalZeroCount_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalZeroCount_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalZeroCount (sixVertexReflectHorizontalField horizontal) = sixVertexHorizontalZeroCount horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalZeroCount_reflect horizontal

/--
[sixVertexHorizontalNontransitionCount_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalNontransitionCount_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalNontransitionCount (sixVertexReflectHorizontalField horizontal) = sixVertexHorizontalNontransitionCount horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalNontransitionCount_reflect horizontal

/--
[sixVertexReflectHorizontalPair_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexReflectHorizontalPair_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectHorizontalPair (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectHorizontalPair_involutive

/--
[sixVertexHorizontalPairBigrade_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalPairBigrade_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairBigrade (sixVertexReflectHorizontalPair horizontal) = sixVertexHorizontalPairBigrade horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairBigrade_reflect horizontal

/--
[sixVertexHorizontalColumnSeamAllowed_reflect_false_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalColumnSeamAllowed_reflect_false_iff_eq
  {T : EvenTorus}
  {i : Fin T.width}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalColumnSeamAllowed (sixVertexReflectHorizontalField horizontal) i false ↔ sixVertexHorizontalColumnSeamAllowed horizontal (finitePeriodicSucc T.width_pos (sixVertexCyclicNeg T.width_pos i)) true := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalColumnSeamAllowed_reflect_false_iff horizontal i

/--
[sixVertexHorizontalColumnSeamAllowed_reflect_true_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalColumnSeamAllowed_reflect_true_iff_eq
  {T : EvenTorus}
  {i : Fin T.width}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalColumnSeamAllowed (sixVertexReflectHorizontalField horizontal) i true ↔ sixVertexHorizontalColumnSeamAllowed horizontal (finitePeriodicSucc T.width_pos (sixVertexCyclicNeg T.width_pos i)) false := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalColumnSeamAllowed_reflect_true_iff horizontal i

/--
[sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {completion : SixVertexVerticalCompletion T horizontal} :
-- imply
  sixVertexHorizontalFalseForcedColumns horizontal = Finset.univ \ sixVertexHorizontalTrueAllowedColumns horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalFalseForcedColumns_eq_compl_trueAllowed completion

/--
[sixVertexVerticalCompletion_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexVerticalCompletion_reflect_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {completion : SixVertexVerticalCompletion T horizontal} :
-- imply
  Nonempty (SixVertexVerticalCompletion T (sixVertexReflectHorizontalField horizontal)) := by
-- proof
  apply StatMech.FrontierD.sixVertexVerticalCompletion_reflect completion

/--
[sixVertexVerticalCompletion_reflect_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexVerticalCompletion_reflect_iff_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  Nonempty (SixVertexVerticalCompletion T (sixVertexReflectHorizontalField horizontal)) ↔ Nonempty (SixVertexVerticalCompletion T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexVerticalCompletion_reflect_iff horizontal

/--
[card_sixVertexHorizontalFreeColumns_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma card_sixVertexHorizontalFreeColumns_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  (sixVertexHorizontalFreeColumns (sixVertexReflectHorizontalField horizontal)).card = (sixVertexHorizontalFreeColumns horizontal).card := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalFreeColumns_reflect horizontal

/--
[card_sixVertexHorizontalForcedTrueColumns_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma card_sixVertexHorizontalForcedTrueColumns_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  (sixVertexHorizontalForcedTrueColumns (sixVertexReflectHorizontalField horizontal)).card = (sixVertexHorizontalFalseForcedColumns horizontal).card := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalForcedTrueColumns_reflect horizontal

/--
[card_sixVertexHorizontalFalseForcedColumns](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma card_sixVertexHorizontalFalseForcedColumns_eq
  {T : EvenTorus}
  {horizontal : SixVertexHorizontalField T}
  {completion : SixVertexVerticalCompletion T horizontal} :
-- imply
  (sixVertexHorizontalFalseForcedColumns horizontal).card = T.width - (sixVertexHorizontalFreeColumns horizontal).card - (sixVertexHorizontalForcedTrueColumns horizontal).card := by
-- proof
  apply StatMech.FrontierD.card_sixVertexHorizontalFalseForcedColumns completion

/--
[sixVertexHorizontalCompletionProfile_ext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalCompletionProfile_ext_eq
  {T : EvenTorus}
  {first second : SixVertexHorizontalCompletionProfile T}
-- given
  (hforced : first.forcedTrue = second.forcedTrue)
  (hfree : first.free = second.free) :
-- imply
  first = second := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalCompletionProfile_ext hforced hfree

/--
[sixVertexReflectHorizontalCompletionProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexReflectHorizontalCompletionProfile_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectHorizontalCompletionProfile (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectHorizontalCompletionProfile_involutive

/--
[sixVertexHorizontalComplementSector_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalComplementSector_involutive_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)} :
-- imply
  sixVertexHorizontalComplementSector T (sixVertexHorizontalComplementSector T sector) = sector := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalComplementSector_involutive T sector

/--
[sixVertexHorizontalProfileChooseCount_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalProfileChooseCount_reflect_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
  {profile : SixVertexHorizontalCompletionProfile T}
-- given
  (hvalid : profile.forcedTrue.val + profile.free.val <= T.width) :
-- imply
  sixVertexHorizontalProfileChooseCount sector (some (sixVertexReflectHorizontalCompletionProfile profile)) = sixVertexHorizontalProfileChooseCount (sixVertexHorizontalComplementSector T sector) (some profile) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalProfileChooseCount_reflect sector profile hvalid

/--
[sixVertexHorizontalCompletionProfile_valid_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalCompletionProfile_valid_of_eq_eq
  {T : EvenTorus}
  {profile : SixVertexHorizontalCompletionProfile T}
-- given
  (horizontal : SixVertexHorizontalField T)
  (hprofile : sixVertexHorizontalCompletionProfile T horizontal = some profile) :
-- imply
  profile.forcedTrue.val + profile.free.val <= T.width := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalCompletionProfile_valid_of_eq horizontal profile hprofile

/--
[sixVertexReflectOptionalHorizontalCompletionProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexReflectOptionalHorizontalCompletionProfile_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectOptionalHorizontalCompletionProfile (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectOptionalHorizontalCompletionProfile_involutive

/--
[sixVertexHorizontalCompletionProfile_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalCompletionProfile_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalCompletionProfile T (sixVertexReflectHorizontalField horizontal) = sixVertexReflectOptionalHorizontalCompletionProfile (sixVertexHorizontalCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalCompletionProfile_reflect horizontal

/--
[sixVertexHorizontalSectorCompletionChooseCount_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalSectorCompletionChooseCount_reflect_eq
  {T : EvenTorus}
  {sector : Fin (T.width + 1)}
-- given
  (horizontal : SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalSectorCompletionChooseCount T sector (sixVertexReflectHorizontalField horizontal) = sixVertexHorizontalSectorCompletionChooseCount T (sixVertexHorizontalComplementSector T sector) horizontal := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalSectorCompletionChooseCount_reflect T sector horizontal

/--
[sixVertexHorizontalChooseSum_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalChooseSum_reflect_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {grade : Nat × Nat} :
-- imply
  (∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T left horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T right horizontal.1.2) = ∑ horizontal : {horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T // sixVertexHorizontalPairBigrade horizontal = grade}, sixVertexHorizontalSectorCompletionChooseCount T (sixVertexHorizontalComplementSector T left) horizontal.1.1 * sixVertexHorizontalSectorCompletionChooseCount T (sixVertexHorizontalComplementSector T right) horizontal.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalChooseSum_reflect T left right grade

/--
[sixVertexReflectHorizontalPairCompletionProfile_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexReflectHorizontalPairCompletionProfile_involutive_eq
  {T : EvenTorus} :
-- imply
  Function.Involutive (sixVertexReflectHorizontalPairCompletionProfile (T := T)) := by
-- proof
  apply StatMech.FrontierD.sixVertexReflectHorizontalPairCompletionProfile_involutive

/--
[sixVertexHorizontalPairCompletionProfile_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalPairCompletionProfile_reflect_eq
  {T : EvenTorus}
-- given
  (horizontal : SixVertexHorizontalField T × SixVertexHorizontalField T) :
-- imply
  sixVertexHorizontalPairCompletionProfile T (sixVertexReflectHorizontalPair horizontal) = sixVertexReflectHorizontalPairCompletionProfile (sixVertexHorizontalPairCompletionProfile T horizontal) := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairCompletionProfile_reflect horizontal

/--
[sixVertexHorizontalPairProfileMultiplicity_reflect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexHorizontalProfileReflection.lean)
-/
@[path]
private lemma sixVertexHorizontalPairProfileMultiplicity_reflect_eq
  {T : EvenTorus}
  {grade : Nat × Nat}
  {profile : SixVertexHorizontalPairCompletionProfile T} :
-- imply
  sixVertexHorizontalPairProfileMultiplicity T grade (sixVertexReflectHorizontalPairCompletionProfile profile) = sixVertexHorizontalPairProfileMultiplicity T grade profile := by
-- proof
  apply StatMech.FrontierD.sixVertexHorizontalPairProfileMultiplicity_reflect T grade profile


-- created on 2026-10-23
