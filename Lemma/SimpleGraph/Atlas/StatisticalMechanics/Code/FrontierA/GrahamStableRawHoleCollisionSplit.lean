import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (huTargetRaw : u.target.1 = (canonicalStableRawReferenceOwnerAlternateData ends m j k l zero hloop hjk hkl hk0 p s hself).target)
  (huStable : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p s u) :
-- imply
  ∃ huDirect : u.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p u.source, (s.source, (canonicalStableRawReferenceOwnerAlternateData ends m j k l zero hloop hjk hkl hk0 p s hself).target) = (u.source, u.target.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerStableOutput_directKey_eq_referenceSource ends m j k l zero hloop hjk hkl hk0 p s u hself huTargetRaw huStable

/--
[canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (huTargetRaw : u.target.1 = (canonicalStableRawReferenceOwnerAlternateData ends m j k l zero hloop hjk hkl hk0 p s hself).target)
  (huAdvancing : CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p s u) :
-- imply
  ∃ huDirect : u.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p u.source, (canonicalStableRawReferenceOwner ends m j k l zero hloop hjk hkl hk0 p s, (canonicalStableRawReferenceOwnerAlternateData ends m j k l zero hloop hjk hkl hk0 p s hself).target) = (u.source, u.target.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerAdvancingOutput_directKey_eq_referenceOwner ends m j k l zero hloop hjk hkl hk0 p s u hself huTargetRaw huAdvancing

/--
[canonicalStableRawReferenceOwnerLeftToken_not_exceptional_of_stableOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_not_exceptional_of_stableOutput_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (huTarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself))
  (huStable : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p s u) :
-- imply
  ¬ CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_not_exceptional_of_stableOutput ends m j k l zero hloop hjk hkl hk0 p s u hself huTarget huStable

/--
[canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_direct_of_stableOutput](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_direct_of_stableOutput_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {direct : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (huTarget : u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision).1)
  (huStable : CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u) :
-- imply
  canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_direct_of_stableOutput ends m j k l zero hloop hjk hkl hk0 p hno component collision u huTarget huStable direct

/--
[canonicalStableRawComponentCollisionCharge_of_referenceOwnerStableOutputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawComponentCollisionCharge_of_referenceOwnerStableOutputs_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstable : ∀ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u) :
-- imply
  CanonicalStableRawComponentCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCollisionCharge_of_referenceOwnerStableOutputs ends m j k l zero hloop hjk hkl hk0 p hno component hstable

/--
[exists_canonicalStableRawComponentReferenceOwnerAdvancingOutput_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentReferenceOwnerAdvancingOutput_of_card_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcard : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  ∃ collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component), ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1 u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentReferenceOwnerAdvancingOutput_of_card_lt ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[exists_canonicalStableRawComponentFirstChargeKeyCollisionSplit_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentFirstChargeKeyCollisionSplit_of_card_lt_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcard : Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) < Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  let directKey := canonicalStableRawComponentDirectKeyEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let firstKey := canonicalStableRawComponentReferenceOwnerKeyEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let sourceFirstKey := canonicalStableRawComponentReferenceSourceFirstKeyEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component Nonempty (StatMech.FrontierA.crossCollision sourceFirstKey directKey) ∨ Nonempty (StatMech.FrontierA.crossCollision firstKey directKey) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentFirstChargeKeyCollisionSplit_of_card_lt ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[canonicalStableRawComponentCrossCollision_stablePair_or_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawComponentCrossCollision_stablePair_or_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (Fin 2 ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) ∨ CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCrossCollision_stablePair_or_advancing ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawStableCrossCollision_selfBase_eq_of_nextTarget_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma canonicalStableRawStableCrossCollision_selfBase_eq_of_nextTarget_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x y : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hx : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
  (hy : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1)
  (htarget : (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1).target) :
-- imply
  canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.source = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p y.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStableCrossCollision_selfBase_eq_of_nextTarget_eq ends m j k l zero hloop hjk hkl hk0 p hno component x y hx hy htarget

/--
[card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {A : Finset (StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component))}
  {x₀ : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hx₀ : x₀ ∈ A)
  (hstable : ∀ x ∈ A, CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
  (htarget : ∀ x ∈ A, (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧ sources.card = A.card ∧ A.card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalRawRelationNeighborhood_of_stableCollisionTargetBlock ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀ hstable htarget

/--
[exists_canonicalRawRelationNeighborhoodEmbedding_of_stableCollisionTargetBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawHoleCollisionSplit.lean)
-/
@[path]
private lemma exists_canonicalRawRelationNeighborhoodEmbedding_of_stableCollisionTargetBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {A : Finset (StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component))}
  {x₀ : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hx₀ : x₀ ∈ A)
  (hstable : ∀ x ∈ A, CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
  (htarget : ∀ x ∈ A, (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1).target = (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1).target) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧ Nonempty (↑A ↪ ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩))) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalRawRelationNeighborhoodEmbedding_of_stableCollisionTargetBlock ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀ hstable htarget


-- created on 2026-10-23
