import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairResolvedInjection
open StatMech StatMech.FrontierD


/--
[sixVertexExplicitResolvedColoredPair_arrows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma sixVertexExplicitResolvedColoredPair_arrows_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat}
  {resolved : SixVertexExplicitResolvedMarkedPair T left right k}
  {layer : Bool} :
-- imply
  (sixVertexExplicitResolvedColoredPair resolved layer).arrows = sixVertexArrowPairLayer resolved.1.1.1.1 resolved.1.1.2.1 layer := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitResolvedColoredPair_arrows resolved layer

/--
[sixVertexExplicitResolvedColoredPair_pairing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma sixVertexExplicitResolvedColoredPair_pairing_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat}
  {resolved : SixVertexExplicitResolvedMarkedPair T left right k}
  {layer : Bool} :
-- imply
  (sixVertexExplicitResolvedColoredPair resolved layer).pairing = sixVertexExplicitResolvedPairing resolved.1.2 resolved.2 layer := by
-- proof
  apply StatMech.FrontierD.sixVertexExplicitResolvedColoredPair_pairing resolved layer

/--
[card_sixVertexExplicitResolvedMarkedPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma card_sixVertexExplicitResolvedMarkedPair_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  Fintype.card (SixVertexExplicitResolvedMarkedPair T left right k) = Fintype.card (SixVertexExplicitMarkedDecoratedPair T left right k) * 2 ^ k := by
-- proof
  apply StatMech.FrontierD.card_sixVertexExplicitResolvedMarkedPair T left right k

/--
[markedResolutionFactor_identity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma markedResolutionFactor_identity_eq
  {total k : Nat} :
-- imply
  (2 ^ (total - k) * total.choose k) * 2 ^ k = 2 ^ total * total.choose k := by
-- proof
  apply StatMech.FrontierD.markedResolutionFactor_identity total k

/--
[card_sixVertexExplicitMarkedDecoratedPair_eq_compact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma card_sixVertexExplicitMarkedDecoratedPair_eq_compact_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  Fintype.card (SixVertexExplicitMarkedDecoratedPair T left right k) = Fintype.card (SixVertexMarkedDecoratedPair T left right k) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexExplicitMarkedDecoratedPair_eq_compact T left right k

/--
[card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {k : Nat}
-- given
  (matching : SixVertexExplicitResolvedMarkedPair T sourceLeft sourceRight k -> SixVertexExplicitResolvedMarkedPair T targetLeft targetRight k)
  (hinjective : Function.Injective matching) :
-- imply
  Fintype.card (SixVertexMarkedDecoratedPair T sourceLeft sourceRight k) <= Fintype.card (SixVertexMarkedDecoratedPair T targetLeft targetRight k) := by
-- proof
  apply StatMech.FrontierD.card_sixVertexMarkedDecoratedPair_le_of_resolvedInjection matching hinjective

/--
[sixVertexMarkedSectorPairMass_le_of_resolvedInjection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_le_of_resolvedInjection_eq
  {T : EvenTorus}
  {sourceLeft sourceRight targetLeft targetRight : Fin (T.width + 1)}
  {k : Nat}
-- given
  (matching : SixVertexExplicitResolvedMarkedPair T sourceLeft sourceRight k -> SixVertexExplicitResolvedMarkedPair T targetLeft targetRight k)
  (hinjective : Function.Injective matching) :
-- imply
  sixVertexMarkedSectorPairMass T sourceLeft sourceRight k <= sixVertexMarkedSectorPairMass T targetLeft targetRight k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_le_of_resolvedInjection matching hinjective

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (matching : forall k : Nat, SixVertexExplicitResolvedMarkedPair T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k -> SixVertexExplicitResolvedMarkedPair T middle middle k)
  (hinjective : forall k, Function.Injective (matching k)) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedInjections T middle hmiddle_pos hmiddle_lt matching hinjective

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairResolvedInjection.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hfiber : SixVertexExplicitResolvedBigradeFiberDominates T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ middle middle) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_resolvedBigradeFibers T middle hmiddle_pos hmiddle_lt hfiber


-- created on 2026-10-23
