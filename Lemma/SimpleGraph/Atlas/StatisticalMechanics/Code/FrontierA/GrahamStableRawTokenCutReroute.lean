import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamStableRawTokenCutReroute
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalStableOccupiedAlternate_opposingCuts_or_twoRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableOccupiedAlternate_opposingCuts_or_twoRow_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
  (hne : c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) :
-- imply
  let hc := canonicalRawCommonClosure_leftGate ends m j k l zero p c.1 c.2 let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d⟩ let hb := canonicalRawCommonClosure_leftGate ends m j k l zero p b.1 b.2 let a := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1 hc let owner := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p b.1 hb let q := (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩ CanonicalOpposingRootCutsAtRight ends m j k l zero p a owner q ∨ CanonicalTightTwoRowCollision ends m j k l zero p a owner := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableOccupiedAlternate_opposingCuts_or_twoRow ends m j k l zero hloop hjk hkl hk0 p c d hcd hne

/--
[canonicalStableRawRightTarget_memClosure_or_positive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawRightTarget_memClosure_or_positive_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W) :
-- imply
  d.1 ∈ canonicalRawCommonClosure ends m j k l zero p ∨ ReversalGatePositive ends m j k l zero p d.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawRightTarget_memClosure_or_positive ends m j k l zero p d

/--
[canonicalStableOccupiedAlternate_positive_or_commonGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableOccupiedAlternate_positive_or_commonGeometry_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
  (hne : c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) :
-- imply
  ReversalGatePositive ends m j k l zero p d.1 ∨ ∃ dCommon : ↑(canonicalRawCommonClosure ends m j k l zero p), dCommon.1 = d.1 ∧ let hc := canonicalRawCommonClosure_leftGate ends m j k l zero p c.1 c.2 let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d⟩ let hb := canonicalRawCommonClosure_leftGate ends m j k l zero p b.1 b.2 let a := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1 hc let owner := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p b.1 hb let q := (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩ CanonicalOpposingRootCutsAtRight ends m j k l zero p a owner q ∨ CanonicalTightTwoRowCollision ends m j k l zero p a owner := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableOccupiedAlternate_positive_or_commonGeometry ends m j k l zero hloop hjk hkl hk0 p c d hcd hne

/--
[canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
  (hne : c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) :
-- imply
  let hc := canonicalRawCommonClosure_leftGate ends m j k l zero p c.1 c.2 let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d⟩ let hb := canonicalRawCommonClosure_leftGate ends m j k l zero p b.1 b.2 let a := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1 hc let owner := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p b.1 hb let q := (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩ CanonicalOpposingRootCutsAtRight ends m j k l zero p a owner q ∨ ∃ e : leftSourceMaskFiber ends m j k l zero p, CanonicalRawGateRelated ends m j k l zero p c.1 e ∧ CanonicalRawGateRelated ends m j k l zero p b.1 e ∧ e ≠ d.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableOccupiedAlternate_opposingCuts_or_distinctReroute ends m j k l zero hloop hjk hkl hk0 p c d hcd hne

/--
[canonicalStableOccupiedAlternate_cut_or_free_or_sameSourceNext](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableOccupiedAlternate_cut_or_free_or_sameSourceNext_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {d : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : CanonicalRawGateRelated ends m j k l zero p c.1 d.1)
  (hne : c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d) :
-- imply
  let hc := canonicalRawCommonClosure_leftGate ends m j k l zero p c.1 c.2 let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p d, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p d⟩ let hb := canonicalRawCommonClosure_leftGate ends m j k l zero p b.1 b.2 let a := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1 hc let owner := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p b.1 hb let q := (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p).symm ⟨d.1, hcd.choose_spec.1⟩ CanonicalOpposingRootCutsAtRight ends m j k l zero p a owner q ∨ ∃ e : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)), e.1 ≠ d.1 ∧ CanonicalRawGateRelated ends m j k l zero p c.1 e.1 ∧ (canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p e = c.1 ∨ c.1 ≠ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p e) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableOccupiedAlternate_cut_or_free_or_sameSourceNext ends m j k l zero hloop hjk hkl hk0 p c d hcd hne

/--
[canonicalStableRawExceptionalEdge_eq_of_source_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdge_eq_of_source_target_eq_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (hsource : s.source = t.source)
  (htarget : s.target = t.target) :
-- imply
  s = t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdge_eq_of_source_target_eq hsource htarget

/--
[canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {hloop : ∀ i ∈ m, ¬ (ends i).IsDiag}
  {hjk : j ≠ k}
  {hkl : k ≠ l}
  {hk0 : k ≠ zero}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (htarget : s.target = t.target) :
-- imply
  s.source ≠ t.source ∨ s = t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdge_source_ne_or_eq_of_target_eq s t htarget

/--
[exists_canonicalStableRawExceptionalEdge_of_distinct_commonTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawExceptionalEdge_of_distinct_commonTarget_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {target : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcd : c ≠ d)
  (hc : CanonicalRawGateRelated ends m j k l zero p c.1 target.1)
  (hd : CanonicalRawGateRelated ends m j k l zero p d.1 target.1) :
-- imply
  ∃ s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, s.target = target ∧ (s.source = c ∨ s.source = d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawExceptionalEdge_of_distinct_commonTarget ends m j k l zero hloop hjk hkl hk0 p c d target hcd hc hd

/--
[exists_canonicalStableRawExceptionalEdge_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawExceptionalEdge_next_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.target⟩ t.target.1 ≠ s.target.1 ∧ CanonicalRawGateRelated ends m j k l zero p s.source.1 t.target.1 ∧ CanonicalRawGateRelated ends m j k l zero p b.1 t.target.1 ∧ (t.source = s.source ∨ t.source = b) ∧ (t.source = b ∨ (t.source = s.source ∧ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p t.target = b.1)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawExceptionalEdge_next ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawCollisionTokenEmbedding_of_weakComponentData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawCollisionTokenEmbedding_of_weakComponentData_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcomponents : CanonicalStableRawWeakComponentTokenEmbeddingData ends m j k l zero hloop hjk hkl hk0 p hno) :
-- imply
  CanonicalStableRawCollisionTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawCollisionTokenEmbedding_of_weakComponentData ends m j k l zero hloop hjk hkl hk0 p hno hcomponents

/--
[canonicalStableRawExceptionalEdgeNext_target_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeNext_target_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s).target.1 ≠ s.target.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeNext_target_ne ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawExceptionalEdgeNext_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeNext_square_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let t := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.target⟩ CanonicalRawGateRelated ends m j k l zero p s.source.1 t.target.1 ∧ CanonicalRawGateRelated ends m j k l zero p b.1 t.target.1 ∧ (t.source = s.source ∨ t.source = b) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeNext_square ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawExceptionalEdgeNext_source_or_owner_stable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeNext_source_or_owner_stable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let t := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.target⟩ t.source = b ∨ (t.source = s.source ∧ canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p t.target = b.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeNext_source_or_owner_stable ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hpreferredSelf : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.target⟩)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s next.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p next.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p next.target⟩ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerStableStep_nextTarget_free_of_preferredSelf ends m j k l zero hloop hjk hkl hk0 p hno s hpreferredSelf hstable

/--
[canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno s ∨ CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeNext_advancing_or_ownerStable ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawOwnerAdvancingStep_rank_lt_of_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawOwnerAdvancingStep_rank_lt_of_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hadvancing : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  canonicalStableRawSourceRank ends m j k l zero p (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s).source < canonicalStableRawSourceRank ends m j k l zero p s.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerAdvancingStep_rank_lt_of_self ends m j k l zero hloop hjk hkl hk0 p hno s hself hadvancing

/--
[canonicalStableRawExceptionalEdgeNext_nonself_of_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeNext_nonself_of_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (next s).target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p (next s).source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeNext_nonself_of_self ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawDirectLeftToken_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectLeftToken_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  Function.Injective fun s : {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source} => canonicalStableRawDirectLeftToken ends m j k l zero hloop hjk hkl hk0 p s.1 s.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectLeftToken_injective ends m j k l zero hloop hjk hkl hk0 p

/--
[canonicalStableRawDirectLeftToken_isExceptional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectLeftToken_isExceptional_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawDirectLeftToken ends m j k l zero hloop hjk hkl hk0 p s hdirect) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectLeftToken_isExceptional ends m j k l zero hloop hjk hkl hk0 p s hdirect

/--
[canonicalStableRawDirectLeftToken_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectLeftToken_component_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawDirectLeftToken ends m j k l zero hloop hjk hkl hk0 p s hdirect) = StatMech.FrontierA.functionWeakComponent (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectLeftToken_component ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  ¬ CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawSelfOwnerRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfOwnerReroute_not_exceptional_of_ownerStable ends m j k l zero hloop hjk hkl hk0 p hno s hself hstable

/--
[canonicalStableRawSelfReroute_eq_directToken_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfReroute_eq_directToken_dichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (tdirect : t.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p t.source)
  (htoken : canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself = canonicalStableRawDirectLeftToken ends m j k l zero hloop hjk hkl hk0 p t tdirect) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (t = next s ∧ CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s) ∨ (CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno s ∧ t.source = s.source ∧ t.target = (next s).target ∧ t ≠ next s) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfReroute_eq_directToken_dichotomy ends m j k l zero hloop hjk hkl hk0 p hno s t hself tdirect htoken

/--
[canonicalStableRawSelfReroute_componentDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfReroute_componentDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno let token := canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself let component := StatMech.FrontierA.functionWeakComponent next ¬ CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p token ∨ canonicalStableRawLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component s ∨ ∃ t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno s ∧ t.source = s.source ∧ t.target = (next s).target ∧ t ≠ next s ∧ canonicalStableRawLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfReroute_componentDichotomy ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawWitnessedStateTokenIncidence_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawWitnessedStateTokenIncidence_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  CanonicalStableRawWitnessedStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s ↔ CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawWitnessedStateTokenIncidence_iff ends m j k l zero hloop hjk hkl hk0 p token s

/--
[mem_canonicalStableRawTokenComponent_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma mem_canonicalStableRawTokenComponent_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  s ∈ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalStableRawTokenComponent_self ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawTokenComponent_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_eq_of_mem_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hst : t ∈ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_eq_of_mem ends m j k l zero hloop hjk hkl hk0 p hno hst

/--
[canonicalStableRawTokenComponent_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_next_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_next ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawTokenComponent_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_iterate_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {n : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_iterate ends m j k l zero hloop hjk hkl hk0 p hno s n

/--
[canonicalStableRawTokenComponent_eq_of_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_eq_of_target_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htarget : s.target = t.target) :
-- imply
  canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_eq_of_target_eq ends m j k l zero hloop hjk hkl hk0 p hno s t htarget

/--
[canonicalStableRawStateTokenIncidence_component_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawStateTokenIncidence_component_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hs : CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s)
  (ht : CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token t) :
-- imply
  canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStateTokenIncidence_component_eq ends m j k l zero hloop hjk hkl hk0 p hno token s t hs ht

/--
[canonicalStableRawDirectLeftToken_collisionClosedComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectLeftToken_collisionClosedComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawCollisionClosedLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawDirectLeftToken ends m j k l zero hloop hjk hkl hk0 p s hdirect) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectLeftToken_collisionClosedComponent ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[canonicalStableRawSelfReroute_collisionClosedComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfReroute_collisionClosedComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself)) :
-- imply
  canonicalStableRawCollisionClosedLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfReroute_collisionClosedComponent ends m j k l zero hloop hjk hkl hk0 p hno s hself hexceptional

/--
[canonicalStableRawSelfReroutePredecessor_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfReroutePredecessor_unique_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hs : CanonicalStableRawSelfReroutePredecessor ends m j k l zero hloop hjk hkl hk0 p hno token s)
  (ht : CanonicalStableRawSelfReroutePredecessor ends m j k l zero hloop hjk hkl hk0 p hno token t) :
-- imply
  s = t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfReroutePredecessor_unique ends m j k l zero hloop hjk hkl hk0 p hno token s t hs ht

/--
[canonicalStableRawSquareOutputPredecessor_component_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSquareOutputPredecessor_component_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hs : CanonicalStableRawSquareOutputPredecessor ends m j k l zero hloop hjk hkl hk0 p hno token s)
  (ht : CanonicalStableRawSquareOutputPredecessor ends m j k l zero hloop hjk hkl hk0 p hno token t) :
-- imply
  canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSquareOutputPredecessor_component_eq ends m j k l zero hloop hjk hkl hk0 p hno token s t hs ht

/--
[canonicalStableRawSelfReroute_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfReroute_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfReroute_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawSelfOwnerReroute_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfOwnerReroute_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawSelfOwnerRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfOwnerReroute_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawExceptionalLeftToken_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalLeftToken_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hexceptional : CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p token) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token (canonicalStableRawExceptionalEdgeOfLeftToken ends m j k l zero hloop hjk hkl hk0 p token hexceptional) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalLeftToken_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token hexceptional

/--
[canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hs : CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawLeftToken_fullComponent_of_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p hno token s hs

/--
[exists_canonicalStableRawOverlapToken_in_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawOverlapToken_in_component_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {target : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcd : c ≠ d)
  (hself : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p d)
  (hc : CanonicalRawGateRelated ends m j k l zero p c.1 target.1)
  (hd : CanonicalRawGateRelated ends m j k l zero p d.1 target.1) :
-- imply
  ∃ (s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p) (token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p), canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token = target ∧ (token.1 = c ∨ token.1 = d) ∧ CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s ∧ canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawOverlapToken_in_component ends m j k l zero hloop hjk hkl hk0 p hno c d target hcd hself hc hd

/--
[canonicalStableRawStateTokenIncidence_outputDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawStateTokenIncidence_outputDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hincidence : CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s) :
-- imply
  ∃ t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, t.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p s t ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p s t) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStateTokenIncidence_outputDichotomy ends m j k l zero hloop hjk hkl hk0 p hno token s hincidence

/--
[canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hs : CanonicalStableRawWitnessedStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token s)
  (ht : CanonicalStableRawWitnessedStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token t) :
-- imply
  s = t ∨ (∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token ∧ CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p s u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t) ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p token ∧ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p s u ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawWitnessedStateTokenIncidence_sharedTokenClassification ends m j k l zero hloop hjk hkl hk0 p hno token s t hs ht

/--
[canonicalStableRawDirectLeftToken_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectLeftToken_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawDirectLeftToken ends m j k l zero hloop hjk hkl hk0 p s hdirect) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[canonicalStableRawSelfReroute_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfReroute_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfReroute_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawSelfOwnerReroute_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfOwnerReroute_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawSelfOwnerRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfOwnerReroute_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawOwnerStableSelfPair_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawOwnerStableSelfPair_componentEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (_hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  Nonempty (Fin 2 ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawOwnerStableSelfPair_componentEmbedding ends m j k l zero hloop hjk hkl hk0 p hno s hself _hstable

/--
[canonicalStableRawStateLeftToken_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawStateLeftToken_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStateLeftToken_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawStateLeftToken_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawStateLeftToken_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStateLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalStableRawSelfState_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfState_componentEmbedding_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty ({s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧ s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source} ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfState_componentEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawDirectState_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectState_componentEmbedding_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty ({s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component ∧ s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source} ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectState_componentEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawStateLeftToken_eq_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawStateLeftToken_eq_imp_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s = canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno t -> s = t ∨ CanonicalStableRawSelfDirectTokenCollision ends m j k l zero hloop hjk hkl hk0 p hno s t ∨ CanonicalStableRawSelfDirectTokenCollision ends m j k l zero hloop hjk hkl hk0 p hno t s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawStateLeftToken_eq_imp ends m j k l zero hloop hjk hkl hk0 p hno s t

/--
[canonicalStableRawSelfDirectTokenCollision_of_token_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawSelfDirectTokenCollision_of_token_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {self direct : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : self.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p self.source)
  (hdirect : direct.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p direct.source)
  (htoken : canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno self = canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno direct) :
-- imply
  CanonicalStableRawSelfDirectTokenCollision ends m j k l zero hloop hjk hkl hk0 p hno self direct := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawSelfDirectTokenCollision_of_token_eq ends m j k l zero hloop hjk hkl hk0 p hno self direct hself hdirect htoken

/--
[canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype C]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm C}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : C -> CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : ∀ x, state (σ x) = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (state x))
  (htarget : Function.Injective fun x => (state x).target)
  (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (state x)) :
-- imply
  Function.Injective fun x => canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno (state x) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalClosedAdvancingExceptionalCycle_stateLeftToken_injective ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep htarget hadvance

/--
[canonicalClosedAdvancingExceptionalCycle_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalClosedAdvancingExceptionalCycle_componentEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype C]
  {root : C}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm C}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : C -> CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : ∀ x, state (σ x) = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (state x))
  (htarget : Function.Injective fun x => (state x).target)
  (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (state x))
  (hcomponent : ∀ x, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (state x) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (state root)) :
-- imply
  Nonempty (C ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (state root)}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalClosedAdvancingExceptionalCycle_componentEmbedding root ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep htarget hadvance hcomponent

/--
[canonicalStableRawExceptionalEdgeNext_twoRowCollision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeNext_twoRowCollision_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let hc := canonicalRawCommonClosure_leftGate ends m j k l zero p s.source.1 s.source.2 let b : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.target⟩ let hb := canonicalRawCommonClosure_leftGate ends m j k l zero p b.1 b.2 CanonicalTightTwoRowCollision ends m j k l zero p (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p s.source.1 hc) (sourceMaskGatePointToLeftMaskFiber ends m j k l zero p b.1 hb) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeNext_twoRowCollision ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[exists_ownerStableSquare_collisionTokens_and_surplusTokens](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_ownerStableSquare_collisionTokens_and_surplusTokens_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let leftBase := canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R ∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase, r0 ≠ r1 ∧ ∃ l0 l1 : StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase, l0 ≠ l1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_ownerStableSquare_collisionTokens_and_surplusTokens ends m j k l zero hloop hjk hkl hk0 p hno s hstable

/--
[exists_two_collisionTokens_of_sameTarget_distinctSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_two_collisionTokens_of_sameTarget_distinctSources_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (htarget : s.target = t.target)
  (hsource : s.source ≠ t.source) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R ∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase, r0 ≠ r1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_two_collisionTokens_of_sameTarget_distinctSources ends m j k l zero hloop hjk hkl hk0 p s t htarget hsource

/--
[ownerStableSquare_twoTokenEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma ownerStableSquare_twoTokenEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno s) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let leftBase := canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R Nonempty (Fin 2 ↪ StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧ Nonempty (Fin 2 ↪ StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.ownerStableSquare_twoTokenEmbeddings ends m j k l zero hloop hjk hkl hk0 p hno s hstable

/--
[canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype C]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm C}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : C -> CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)
  (hσ : ∀ x, σ x ≠ x)
  (hstep : ∀ x, state (σ x) = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (state x))
  (htarget : Function.Injective fun x => (state x).target)
  (hadvance : ∀ x, CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (state x)) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let leftBase := canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R Nonempty (C ↪ StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧ Nonempty (C ↪ StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalClosedAdvancingExceptionalCycle_tokenEmbeddings ends m j k l zero hloop hjk hkl hk0 p hno σ state hσ hstep htarget hadvance

/--
[canonicalClosedPreferredSelfExceptionalCycle_tokenEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalClosedPreferredSelfExceptionalCycle_tokenEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype C]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm C}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : C -> CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)
  (hσ : ∀ x, σ x ≠ x)
  (hstep : ∀ x, state (σ x) = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (state x))
  (htarget : Function.Injective fun x => (state x).target)
  (hpreferredSelf : ∀ x, (state x).target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (state x).target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (state x).target⟩) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let leftBase := canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R Nonempty (C ↪ StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧ Nonempty (C ↪ StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalClosedPreferredSelfExceptionalCycle_tokenEmbeddings ends m j k l zero hloop hjk hkl hk0 p hno σ state hσ hstep htarget hpreferredSelf

/--
[canonicalClosedPreferredSelfExceptionalCycle_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalClosedPreferredSelfExceptionalCycle_componentEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype C]
  {root : C}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm C}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (state : C -> CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)
  (hstep : ∀ x, state (σ x) = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (state x))
  (htarget : Function.Injective fun x => (state x).target)
  (hpreferredSelf : ∀ x, (state x).target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p (state x).target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p (state x).target⟩)
  (hcomponent : ∀ x, canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (state x) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (state root)) :
-- imply
  Nonempty (C ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (state root)}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalClosedPreferredSelfExceptionalCycle_componentEmbedding root ends m j k l zero hloop hjk hkl hk0 p hno σ state hstep htarget hpreferredSelf hcomponent

/--
[symmDiffFold_exceptionalCycle_endpointRows_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma symmDiffFold_exceptionalCycle_endpointRows_eq_empty_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {m : Finset I}
  {σ : Equiv.Perm A}
-- given
  (source owner : A -> ↑m -> Fin 4)
  (hadvance : ∀ x, source (σ x) = owner x) :
-- imply
  symmDiffFold Finset.univ (fun x => rowClass m (source x) 0 ∆ rowClass m (owner x) 0) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiffFold_exceptionalCycle_endpointRows_eq_empty m σ source owner hadvance

/--
[exists_referenceTransferFold_eq_of_indexedTranslatedRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_referenceTransferFold_eq_of_indexedTranslatedRows_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {σ : Equiv.Perm A}
-- given
  (ends : I -> Sym2 W)
  (source : A -> leftMaskFiber ends m j k l zero p)
  (hrows : ∀ x : A, ∃ a b : leftMaskFiber ends m j k l zero p, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero a.1.1 (source x).1.1) k zero ∧ canonicalTranslatedRow ends m k zero a.1.1 (source x).1.1 = canonicalTranslatedRow ends m k zero b.1.1 (source (σ x)).1.1) :
-- imply
  ∃ a b : A -> leftMaskFiber ends m j k l zero p, (∀ x, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero (a x).1.1 (source x).1.1) k zero) ∧ (∀ x, canonicalTranslatedRow ends m k zero (a x).1.1 (source x).1.1 = canonicalTranslatedRow ends m k zero (b x).1.1 (source (σ x)).1.1) ∧ symmDiffFold Finset.univ (fun x => canonicalTransferUnion ends m k zero (a x).1.1) = symmDiffFold Finset.univ (fun x => canonicalTransferUnion ends m k zero (b x).1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_referenceTransferFold_eq_of_indexedTranslatedRows ends m j k l zero p source σ hrows

/--
[exists_canonicalStableRawExceptionalEdge_iterate_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawExceptionalEdge_iterate_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let E := CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ∃ i j : Fin (Fintype.card E + 1), i ≠ j ∧ next^[i.1] s = next^[j.1] s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawExceptionalEdge_iterate_repeat ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[exists_canonicalStableRawExceptionalEdge_target_iterate_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawExceptionalEdge_target_iterate_repeat_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)) let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ∃ i j : Fin (Fintype.card U + 1), i ≠ j ∧ (next^[i.1] s).target = (next^[j.1] s).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawExceptionalEdge_target_iterate_repeat ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)) let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ∃ i j : Nat, i < j ∧ j ≤ Fintype.card U ∧ (next^[i] s).target = (next^[j] s).target ∧ ∀ a b : Nat, a < b -> b < j -> (next^[a] s).target ≠ (next^[b] s).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawExceptionalEdge_minimalTargetRepeat ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[exists_canonicalStableRawExceptionalEdge_minimalCycleDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawExceptionalEdge_minimalCycleDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let U := ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p)) let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno ∃ start stop : Nat, start < stop ∧ stop ≤ Fintype.card U ∧ (next^[start] s).target = (next^[stop] s).target ∧ (∀ a b : Nat, a < b -> b < stop -> (next^[a] s).target ≠ (next^[b] s).target) ∧ ((∃ n : Nat, start ≤ n ∧ n < stop ∧ CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)) ∨ ∀ n : Nat, start ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno (next^[n] s)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawExceptionalEdge_minimalCycleDichotomy ends m j k l zero hloop hjk hkl hk0 p hno s

/--
[canonicalMinimalClosedAdvancingCycle_tokenEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalMinimalClosedAdvancingCycle_tokenEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {start stop : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstartStop : start < stop)
  (hstate : ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s) = ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s))
  (hdistinct : ∀ a b : Nat, start ≤ a -> a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
  (hadvance : ∀ n : Nat, start ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let leftBase := canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R Nonempty (Fin (stop - start) ↪ StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧ Nonempty (Fin (stop - start) ↪ StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMinimalClosedAdvancingCycle_tokenEmbeddings ends m j k l zero hloop hjk hkl hk0 p hno s start stop hstartStop hstate hdistinct hadvance

/--
[canonicalMinimalClosedAdvancingCycle_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalMinimalClosedAdvancingCycle_componentEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {start stop : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstartStop : start < stop)
  (hstate : ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s) = ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s))
  (hdistinct : ∀ a b : Nat, start ≤ a -> a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
  (hadvance : ∀ n : Nat, start ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
-- imply
  Nonempty (Fin (stop - start) ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s)}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMinimalClosedAdvancingCycle_componentEmbedding ends m j k l zero hloop hjk hkl hk0 p hno s start stop hstartStop hstate hdistinct hadvance

/--
[canonicalMinimalAdvancingRepeat_componentDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalMinimalAdvancingRepeat_componentDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {start stop : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstartStop : start < stop)
  (hrepeat : ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target = ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
  (hadvance : ∀ n : Nat, start ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno (((next^[start] s).source ≠ (next^[stop] s).source) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (next^[stop] s)) ∨ Nonempty (Fin (stop - start) ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s)}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMinimalAdvancingRepeat_componentDichotomy ends m j k l zero hloop hjk hkl hk0 p hno s start stop hstartStop hrepeat hdistinct hadvance

/--
[canonicalSameTargetDistinctExceptionalPair_componentEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalSameTargetDistinctExceptionalPair_componentEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htarget : s.target = t.target)
  (hsource : s.source ≠ t.source) :
-- imply
  Nonempty (Fin 2 ↪ {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSameTargetDistinctExceptionalPair_componentEmbedding ends m j k l zero hloop hjk hkl hk0 p hno s t htarget hsource

/--
[canonicalMinimalAdvancingRepeat_componentEmbeddingDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalMinimalAdvancingRepeat_componentEmbeddingDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {start stop : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstartStop : start < stop)
  (hrepeat : ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target = ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
  (hadvance : ∀ n : Nat, start ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno Nonempty (Fin 2 ↪ {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s)}) ∨ Nonempty (Fin (stop - start) ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (next^[start] s)}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMinimalAdvancingRepeat_componentEmbeddingDichotomy ends m j k l zero hloop hjk hkl hk0 p hno s start stop hstartStop hrepeat hdistinct hadvance

/--
[canonicalMinimalAdvancingRepeat_tokenDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalMinimalAdvancingRepeat_tokenDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {start stop : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstartStop : start < stop)
  (hrepeat : ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target = ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
  (hadvance : ∀ n : Nat, start ≤ n -> n < stop -> CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
-- imply
  let T := canonicalRawCommonClosure ends m j k l zero p let R := CanonicalRawGateRelated ends m j k l zero p let U := StatMech.FrontierA.finiteRelationNeighborhood R T let leftBase := canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p let rightBase := canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p letI : DecidableEq (leftSourceMaskFiber ends m j k l zero p) := Classical.decEq _ letI : DecidableRel R := Classical.decRel R (∃ r0 r1 : StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase, r0 ≠ r1) ∨ (Nonempty (Fin (stop - start) ↪ StatMech.FrontierA.bipartiteRightCollisionToken R T U rightBase) ∧ Nonempty (Fin (stop - start) ↪ StatMech.FrontierA.bipartiteLeftSurplusToken R T leftBase)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMinimalAdvancingRepeat_tokenDichotomy ends m j k l zero hloop hjk hkl hk0 p hno s start stop hstartStop hrepeat hdistinct hadvance

/--
[ownerStableSquare_targets_isolated_in_minimalCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma ownerStableSquare_targets_isolated_in_minimalCycle_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
  {start stop n : Nat}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hstartStop : start < stop)
  (hnStart : start ≤ n)
  (hnStop : n < stop)
  (hrepeat : ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[start] s).target = ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[stop] s).target)
  (hdistinct : ∀ a b : Nat, a < b -> b < stop -> ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[a] s).target ≠ ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[b] s).target)
  (hstable : CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno ((canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno)^[n] s)) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno let succIndex := if n + 1 < stop then n + 1 else start ∀ q : Nat, start ≤ q -> q < stop -> q ≠ n -> q ≠ succIndex -> (next^[q] s).target ≠ (next^[n] s).target ∧ (next^[q] s).target ≠ (next^[n + 1] s).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.ownerStableSquare_targets_isolated_in_minimalCycle ends m j k l zero hloop hjk hkl hk0 p hno s start stop n hstartStop hnStart hnStop hrepeat hdistinct hstable

/--
[canonicalSelfImageFiber_referenceTransfer_common_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalSelfImageFiber_referenceTransfer_common_ne_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {q r : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hqr : q ≠ r)
  (himage : (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p q q (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 = (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p r r (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
-- imply
  let hworks := (canonicalSelfTransfer_collision_oppositeWorks ends m j k l zero hloop hjk hkl hk0 p q r himage).1 let alt := canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p r q hworks let self := canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p q q (canonicalTransferWorks_self hloop hjk hkl hk0 q) alt ∈ canonicalMaskRightImages ends m j k l zero p q ∧ alt ∈ canonicalMaskRightImages ends m j k l zero p r ∧ alt ≠ self := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfImageFiber_referenceTransfer_common_ne_self ends m j k l zero hloop hjk hkl hk0 p q r hqr himage

/--
[canonicalStableRawReferenceAlternateData_target_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceAlternateData_target_comm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c r : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcr : c ≠ r)
  (hbase : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r) :
-- imply
  (canonicalStableRawReferenceAlternateData ends m j k l zero hloop hjk hkl hk0 p c r hcr hbase).target = (canonicalStableRawReferenceAlternateData ends m j k l zero hloop hjk hkl hk0 p r c hcr.symm hbase.symm).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceAlternateData_target_comm ends m j k l zero hloop hjk hkl hk0 p c r hcr hbase

/--
[canonicalStableRawReferenceAlternateData_target_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceAlternateData_target_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d r : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcr : c ≠ r)
  (hdr : d ≠ r)
  (hbasec : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r)
  (hbased : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p d = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r)
  (htarget : (canonicalStableRawReferenceAlternateData ends m j k l zero hloop hjk hkl hk0 p c r hcr hbasec).target = (canonicalStableRawReferenceAlternateData ends m j k l zero hloop hjk hkl hk0 p d r hdr hbased).target) :
-- imply
  c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceAlternateData_target_injective ends m j k l zero hloop hjk hkl hk0 p c d r hcr hdr hbasec hbased htarget

/--
[canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d r q : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcr : c ≠ r)
  (hdq : d ≠ q)
  (hbasec : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r)
  (hbased : canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p d = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p q)
  (hrq : r = q)
  (htarget : (canonicalStableRawReferenceAlternateData ends m j k l zero hloop hjk hkl hk0 p c r hcr hbasec).target = (canonicalStableRawReferenceAlternateData ends m j k l zero hloop hjk hkl hk0 p d q hdq hbased).target) :
-- imply
  c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceAlternateData_target_injective_of_reference_eq ends m j k l zero hloop hjk hkl hk0 p c d r q hcr hdq hbasec hbased hrq htarget

/--
[canonicalStableRawReferenceOwner_source_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwner_source_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  s.source ≠ canonicalStableRawReferenceOwner ends m j k l zero hloop hjk hkl hk0 p s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwner_source_ne ends m j k l zero hloop hjk hkl hk0 p s

/--
[canonicalStableRawReferenceOwner_selfBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwner_selfBase_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawReferenceOwner ends m j k l zero hloop hjk hkl hk0 p s) = s.target.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwner_selfBase ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceOwner_sourceBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwner_sourceBase_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawReferenceOwner ends m j k l zero hloop hjk hkl hk0 p s) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwner_sourceBase ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceOwnerLeftToken_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_source_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself).1 = canonicalStableRawReferenceOwner ends m j k l zero hloop hjk hkl hk0 p s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_source ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceOwnerLeftToken_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_target_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself).2.1 = (canonicalStableRawReferenceOwnerAlternateData ends m j k l zero hloop hjk hkl hk0 p s hself).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_target ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceOwnerLeftToken_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawReferenceOwnerLeftToken_eq_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_eq_imp_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hselfS : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hselfT : t.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p t.source)
  (htoken : canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hselfS = canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p t hselfT) :
-- imply
  s = t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_eq_imp ends m j k l zero hloop hjk hkl hk0 p s t hselfS hselfT htoken

/--
[canonicalStableRawReferenceSourceLeftToken_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceSourceLeftToken_source_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  (canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself).1 = s.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceSourceLeftToken_source ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceSourceLeftToken_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceSourceLeftToken_target_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  (canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself).2.1 = (canonicalStableRawReferenceOwnerAlternateData ends m j k l zero hloop hjk hkl hk0 p s hself).target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceSourceLeftToken_target ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceSourceLeftToken_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p s hself

/--
[canonicalStableRawReferenceSourceLeftToken_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceSourceLeftToken_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceSourceLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s hself

/--
[canonicalStableRawReferenceSourceLeftToken_eq_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceSourceLeftToken_eq_imp_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s t : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hselfS : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hselfT : t.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p t.source)
  (htoken : canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p s hselfS = canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p t hselfT) :
-- imply
  s = t := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceSourceLeftToken_eq_imp ends m j k l zero hloop hjk hkl hk0 p s t hselfS hselfT htoken

/--
[canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hself : s.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source)
  (hsource : canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself = canonicalStableRawSelfRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself) :
-- imply
  canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p s hself = canonicalStableRawSelfOwnerRerouteLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hself := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawReferenceOwnerLeftToken_eq_selfOwnerReroute ends m j k l zero hloop hjk hkl hk0 p hno s hself hsource

/--
[canonicalStableRawDirectAlternateLeftToken_source_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectAlternateLeftToken_source_split_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno s let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p s.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p s.target⟩ (next.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source ∧ (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).1 = owner) ∨ (next.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source ∧ (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect).1 = s.source) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectAlternateLeftToken_source_split ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectAlternateLeftToken_stateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[canonicalStableRawDirectAlternateLeftToken_ne_natural](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectAlternateLeftToken_ne_natural_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect ≠ canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectAlternateLeftToken_ne_natural ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[canonicalStableRawDirectAlternateLeftToken_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawDirectAlternateLeftToken_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hdirect : s.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p s.source) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawDirectAlternateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s hdirect) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawDirectAlternateLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s hdirect

/--
[card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset ↑(canonicalRawCommonClosure ends m j k l zero p)}
  {r : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfiber : ∀ c ∈ S, canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p c = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r) :
-- imply
  S.card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (S.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalRawRelationNeighborhood_of_selfBaseFiber ends m j k l zero hloop hjk hkl hk0 p S r hfiber

/--
[canonicalStableRawComponentSelfEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSelfEmbedding_apply_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component s).1 = canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSelfEmbedding_apply ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentDirectEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentDirectEmbedding_apply_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component s).1 = canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentDirectEmbedding_apply ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x).1 = canonicalStableRawReferenceOwnerLeftToken ends m j k l zero hloop hjk hkl hk0 p x.1.1.1 x.1.1.2.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceOwnerCollisionEmbedding_apply ends m j k l zero hloop hjk hkl hk0 p hno component x

/--
[canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x ≠ canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceOwnerCollisionEmbedding_ne_self ends m j k l zero hloop hjk hkl hk0 p hno component x self

/--
[canonicalStableRawComponentReferenceOwner_directOccupant_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceOwner_directOccupant_source_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  collision.1.2.1.source.1 = canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1.1.1.target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceOwner_directOccupant_source ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x).1 = canonicalStableRawReferenceSourceLeftToken ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.1.1 x.1.1.1.1.2.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSourceCollisionEmbedding_apply ends m j k l zero hloop hjk hkl hk0 p hno component x

/--
[canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_first_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x ≠ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_first ends m j k l zero hloop hjk hkl hk0 p hno component x

/--
[canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {old : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x ≠ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component old := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_firstRange ends m j k l zero hloop hjk hkl hk0 p hno component x old

/--
[canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_occupant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_occupant_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSourceCollisionEmbedding_ne_occupant ends m j k l zero hloop hjk hkl hk0 p hno component x

/--
[canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {self : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcollision : canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component x = canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component self) :
-- imply
  self.1 = x.1.1.1.1.1 ∧ CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1.1.1 ∧ x.1.2.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_selfCollision_forces_advancing ends m j k l zero hloop hjk hkl hk0 p hno component x self hcollision

/--
[canonicalStableRawComponentReferenceSource_selfCollision_next_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_selfCollision_next_injective_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Function.Injective fun collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) => canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1.1.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_selfCollision_next_injective ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawComponentReferenceSource_directCollision_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_directCollision_source_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  collision.1.2.1.source = collision.1.1.1.1.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_directCollision_source ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentReferenceSource_directCollision_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_directCollision_target_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  collision.1.2.1.target = collision.1.1.1.2.1.target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_directCollision_target ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1.source = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p collision.1.1.1.2.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_directCollision_selfBase_eq ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentReferenceSource_directCollision_threeSources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_directCollision_threeSources_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ owner : ↑(canonicalRawCommonClosure ends m j k l zero p), collision.1.2.1.source ≠ collision.1.1.1.2.1.source ∧ collision.1.2.1.source ≠ owner ∧ collision.1.1.1.2.1.source ≠ owner ∧ CanonicalRawGateRelated ends m j k l zero p collision.1.2.1.source.1 collision.1.2.1.target.1 ∧ CanonicalRawGateRelated ends m j k l zero p collision.1.1.1.2.1.source.1 collision.1.2.1.target.1 ∧ CanonicalRawGateRelated ends m j k l zero p owner.1 collision.1.2.1.target.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_directCollision_threeSources ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentReferenceSource_directCollision_three_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentReferenceSource_directCollision_three_le_degree_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let degree : Nat := by classical exact ((canonicalRawCommonClosure ends m j k l zero p).filter (fun c => CanonicalRawGateRelated ends m j k l zero p c collision.1.2.1.target.1)).card 3 ≤ degree := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentReferenceSource_directCollision_three_le_degree ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawResidualTargetBlock_two_mul_card_add_one_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawResidualTargetBlock_two_mul_card_add_one_le_degree_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {A : Finset (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component))}
  {x₀ : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target) :
-- imply
  let degree : Nat := by classical exact ((canonicalRawCommonClosure ends m j k l zero p).filter (fun c => CanonicalRawGateRelated ends m j k l zero p c x₀.1.2.1.target.1)).card 2 * A.card + 1 ≤ degree := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawResidualTargetBlock_two_mul_card_add_one_le_degree ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ htarget

/--
[card_le_canonicalRawRelationNeighborhood_of_residualTargetFiberBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma card_le_canonicalRawRelationNeighborhood_of_residualTargetFiberBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {A : Finset (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component))}
  {x₀ : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
  {r : ↑(canonicalRawCommonClosure ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (htarget : ∀ x ∈ A, x.1.2.1.target = x₀.1.2.1.target)
  (hbase : ∀ x ∈ A, canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p x.1.2.1.source = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p r) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), sources.card = 2 * A.card ∧ sources.card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalRawRelationNeighborhood_of_residualTargetFiberBlock ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ htarget r hbase

/--
[canonicalStableRaw_referenceSourceDirectCollision_card_add_le_direct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRaw_referenceSourceDirectCollision_card_add_le_direct_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nat.card (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) + Nat.card (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) ≤ Nat.card (CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRaw_referenceSourceDirectCollision_card_add_le_direct ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionAlternateToken_ne_occupant ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentSecondCollisionAlternateToken_ne_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionAlternateToken_ne_first_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠ canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionAlternateToken_ne_first ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentSecondCollisionAlternateToken_merge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionAlternateToken_merge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {x y : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hxy : canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component x = canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component y) :
-- imply
  x.1.2.1 = y.1.2.1 ∨ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p x.1.2.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p x.1.2.1 u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionAlternateToken_merge ends m j k l zero hloop hjk hkl hk0 p hno component x y hxy

/--
[canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component collision).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionAlternateToken_outputDichotomy ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentSecondCollisionAlternateFiber_outputBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionAlternateFiber_outputBlock_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcollision : collision ∈ canonicalStableRawComponentSecondCollisionAlternateFiber ends m j k l zero hloop hjk hkl hk0 p hno component anchor) :
-- imply
  ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p collision.1.2.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionAlternateFiber_outputBlock ends m j k l zero hloop hjk hkl hk0 p hno component anchor collision hcollision

/--
[canonicalStableRawComponentSecondCollisionAlternateFiber_source_or_owner](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionAlternateFiber_source_or_owner_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {anchor collision : StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcollision : collision ∈ canonicalStableRawComponentSecondCollisionAlternateFiber ends m j k l zero hloop hjk hkl hk0 p hno component anchor) :
-- imply
  let direct := collision.1.2 let next := canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno direct.1 let owner : ↑(canonicalRawCommonClosure ends m j k l zero p) := ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p direct.1.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p direct.1.target⟩ (next.target.1 = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p direct.1.source ∧ owner = (canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1.1) ∨ (next.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p direct.1.source ∧ direct.1.source = (canonicalStableRawComponentSecondCollisionAlternateToken ends m j k l zero hloop hjk hkl hk0 p hno component anchor).1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionAlternateFiber_source_or_owner ends m j k l zero hloop hjk hkl hk0 p hno component anchor collision hcollision

/--
[canonicalStableRawPreferredFreeLeftToken_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawPreferredFreeLeftToken_target_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {target : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfree : target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p target⟩) :
-- imply
  canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawPreferredFreeLeftToken ends m j k l zero hloop hjk hkl hk0 p target hfree) = target := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredFreeLeftToken_target ends m j k l zero hloop hjk hkl hk0 p target hfree

/--
[canonicalStableRawPreferredFreeLeftToken_not_exceptional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawPreferredFreeLeftToken_not_exceptional_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {target : ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (canonicalRawCommonClosure ends m j k l zero p))}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfree : target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p target⟩) :
-- imply
  ¬ CanonicalStableRawLeftTokenIsExceptional ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawPreferredFreeLeftToken ends m j k l zero hloop hjk hkl hk0 p target hfree) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredFreeLeftToken_not_exceptional ends m j k l zero hloop hjk hkl hk0 p target hfree

/--
[canonicalStableRawPreferredFreeLeftToken_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawPreferredFreeLeftToken_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfree : u.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p u.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p u.target⟩) :
-- imply
  CanonicalStableRawStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p (canonicalStableRawPreferredFreeLeftToken ends m j k l zero hloop hjk hkl hk0 p u.target hfree) u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredFreeLeftToken_incident ends m j k l zero hloop hjk hkl hk0 p u hfree

/--
[canonicalStableRawPreferredFreeLeftToken_fullComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawPreferredFreeLeftToken_fullComponent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hfree : u.target.1 ≠ canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p ⟨canonicalStableRawPreferredRightBase ends m j k l zero hloop hjk hkl hk0 p u.target, canonicalStableRawPreferredRightBase_mem ends m j k l zero hloop hjk hkl hk0 p u.target⟩) :
-- imply
  canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno (canonicalStableRawPreferredFreeLeftToken ends m j k l zero hloop hjk hkl hk0 p u.target hfree) = canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawPreferredFreeLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno u hfree

/--
[canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint_eq
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
  (hdisjoint : ∀ collision direct, canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) :
-- imply
  CanonicalStableRawComponentSecondCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionCharge_of_sourceDirectDisjoint ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint

/--
[canonicalStableRawComponentSecondCollisionCharge_of_cardLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionCharge_of_cardLE_eq
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
  (hcard : Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ≤ Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component)) :
-- imply
  CanonicalStableRawComponentSecondCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionCharge_of_cardLE ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[canonicalStableRawComponentCrossCollision_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentCrossCollision_classification_eq
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
  CanonicalStableRawSelfDirectTokenCollision ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 collision.1.2.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCrossCollision_classification ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentCrossCollision_stable_or_advancing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentCrossCollision_stable_or_advancing_eq
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
  CanonicalStableRawOwnerStableStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 ∨ CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno collision.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCrossCollision_stable_or_advancing ends m j k l zero hloop hjk hkl hk0 p hno component collision

/--
[canonicalStableRawComponentCrossCollision_source_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentCrossCollision_source_injective_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Function.Injective fun x : StatMech.FrontierA.crossCollision (canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) => x.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentCrossCollision_source_injective ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq_eq
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
  (hx : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
  (hy : CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1)
  (hnext : canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno y.1.1.1) :
-- imply
  canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p x.1.1.1.source = canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p y.1.1.1.source := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawAdvancingCrossCollision_selfBase_eq_of_next_eq ends m j k l zero hloop hjk hkl hk0 p hno component x y hx hy hnext

/--
[card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock_eq
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
  (hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
  (hnext : ∀ x ∈ A, canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧ sources.card = A.card ∧ A.card ≤ (StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalRawRelationNeighborhood_of_advancingCollisionBlock ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀ hadvancing hnext

/--
[exists_canonicalRawRelationNeighborhoodEmbedding_of_advancingCollisionBlock](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalRawRelationNeighborhoodEmbedding_of_advancingCollisionBlock_eq
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
  (hadvancing : ∀ x ∈ A, CanonicalStableRawOwnerAdvancingStep ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1)
  (hnext : ∀ x ∈ A, canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x.1.1.1 = canonicalStableRawExceptionalEdgeNext ends m j k l zero hloop hjk hkl hk0 p hno x₀.1.1.1) :
-- imply
  ∃ sources : Finset ↑(canonicalRawCommonClosure ends m j k l zero p), (∀ c, c ∈ sources ↔ ∃ x ∈ A, x.1.1.1.source = c) ∧ Nonempty (↑A ↪ ↑(StatMech.FrontierA.finiteRelationNeighborhood (CanonicalRawGateRelated ends m j k l zero p) (sources.map ⟨Subtype.val, Subtype.val_injective⟩))) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalRawRelationNeighborhoodEmbedding_of_advancingCollisionBlock ends m j k l zero hloop hjk hkl hk0 p hno component A x₀ hx₀ hadvancing hnext

/--
[canonicalStableRawTokenComponent_embedding_of_sumEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_sumEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {merged : CanonicalStableRawComponentSelfState ends m j k l zero hloop hjk hkl hk0 p hno component ⊕ CanonicalStableRawComponentDirectState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_sumEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component merged

/--
[canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge_eq
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
  (hcharge : CanonicalStableRawComponentSecondCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_secondCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component hcharge

/--
[canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint_eq
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
  (hdisjoint : ∀ collision direct, canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component collision ≠ canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component direct) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_sourceDirectDisjoint ends m j k l zero hloop hjk hkl hk0 p hno component hdisjoint

/--
[canonicalStableRawComponentSecondCollisionCharge_iff_cardLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentSecondCollisionCharge_iff_cardLE_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawComponentSecondCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component ↔ Fintype.card (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component) ≤ Fintype.card (CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentSecondCollisionCharge_iff_cardLE ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawTokenComponent_embedding_of_collisionCharge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_collisionCharge_eq
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
  (hcharge : CanonicalStableRawComponentCollisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component) :
-- imply
  Nonempty (CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component ↪ CanonicalStableRawComponentToken ends m j k l zero hloop hjk hkl hk0 p hno component) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_collisionCharge ends m j k l zero hloop hjk hkl hk0 p hno component hcharge

/--
[canonicalStableRawComponentNaturalToken_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentNaturalToken_incident_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {s : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component s (canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component s) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component s

/--
[exists_canonicalStableRawComponentPartialMatching_saturating](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentPartialMatching_saturating_eq
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
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let State := {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component} let Token := {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component} let incident : State -> Token -> Prop := fun s token => CanonicalStableRawWitnessedStateTokenIncidence ends m j k l zero hloop hjk hkl hk0 p token.1 s.1 ∃ matching : StatMech.FrontierA.RelationPartialMatching incident, matching.IsMaximum ∧ ∀ s, s ∉ matching.support -> ∃ t, matching.toFun t = some (⟨canonicalStableRawStateLeftToken ends m j k l zero hloop hjk hkl hk0 p hno s.1, (canonicalStableRawStateLeftToken_fullComponent ends m j k l zero hloop hjk hkl hk0 p hno s.1).trans s.2⟩ : Token) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentPartialMatching_saturating ends m j k l zero hloop hjk hkl hk0 p hno component

/--
[canonicalStableRawComponentHoleMove_classification](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawComponentHoleMove_classification_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p)}
  {state : StatMech.FrontierA.RelationPartialMatching.HoleState (CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p) :
-- imply
  let natural := canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component let hnatural := canonicalStableRawComponentNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component let moved := state.move natural hnatural state.hole ≠ moved.hole ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (natural state.hole).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawComponentHoleMove_classification ends m j k l zero hloop hjk hkl hk0 p hno component state

/--
[exists_canonicalStableRawComponentCrossCollision_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentCrossCollision_of_card_lt_eq
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
  let selfMap := canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let directMap := canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let incident := CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component let natural := canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component let hnatural := canonicalStableRawComponentNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ collision : StatMech.FrontierA.crossCollision selfMap directMap, state.hole.1 = collision.1.1.1 ∧ (state.move natural hnatural).hole.1 = collision.1.2.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentCrossCollision_of_card_lt ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[exists_canonicalStableRawComponentFirstChargeOccupant_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentFirstChargeOccupant_of_card_lt_eq
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
  let selfMap := canonicalStableRawComponentSelfEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let directMap := canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let first := canonicalStableRawComponentReferenceOwnerCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component let incident := CanonicalStableRawComponentIncident ends m j k l zero hloop hjk hkl hk0 p hno component let natural := canonicalStableRawComponentNaturalToken ends m j k l zero hloop hjk hkl hk0 p hno component let hnatural := canonicalStableRawComponentNaturalToken_incident ends m j k l zero hloop hjk hkl hk0 p hno component ∃ state : StatMech.FrontierA.RelationPartialMatching.HoleState incident, ∃ collision : StatMech.FrontierA.crossCollision selfMap directMap, ∃ third : CanonicalStableRawComponentState ends m j k l zero hloop hjk hkl hk0 p hno component, state.hole.1 = collision.1.1.1 ∧ (state.move natural hnatural).hole.1 = collision.1.2.1 ∧ state.matching.toFun third = some (first collision) ∧ third ≠ state.hole ∧ third ≠ (state.move natural hnatural).hole ∧ ∃ u : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p, u.target = canonicalStableRawLeftTokenTarget ends m j k l zero hloop hjk hkl hk0 p (first collision).1 ∧ (CanonicalStableRawOwnerStableOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u ∨ CanonicalStableRawOwnerAdvancingOutput ends m j k l zero hloop hjk hkl hk0 p state.hole.1 u) ∧ canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno u = component := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentFirstChargeOccupant_of_card_lt ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[exists_canonicalStableRawComponentResidualCollision_of_card_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma exists_canonicalStableRawComponentResidualCollision_of_card_lt_eq
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
  Nonempty (StatMech.FrontierA.crossCollision (canonicalStableRawComponentReferenceSourceCollisionEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component) (canonicalStableRawComponentDirectEmbedding ends m j k l zero hloop hjk hkl hk0 p hno component)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalStableRawComponentResidualCollision_of_card_lt ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[canonicalStableRawTokenComponent_embedding_of_cardLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawTokenComponent_embedding_of_cardLE_eq
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
  (hcard : Fintype.card {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤ Fintype.card {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
-- imply
  Nonempty ({s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component} ↪ {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component}) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawTokenComponent_embedding_of_cardLE ends m j k l zero hloop hjk hkl hk0 p hno component hcard

/--
[canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcard : ∀ component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p), Fintype.card {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤ Fintype.card {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
-- imply
  Nonempty (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p ↪ CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawExceptionalEdgeEmbedding_of_componentCardLE ends m j k l zero hloop hjk hkl hk0 p hno hcard

/--
[canonicalStableRawCollisionTokenEmbedding_of_componentCardLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawTokenCutReroute.lean)
-/
@[path]
private lemma canonicalStableRawCollisionTokenEmbedding_of_componentCardLE_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : CanonicalStableRawNoOpposingCuts ends m j k l zero hloop hjk hkl hk0 p)
  (hcard : ∀ component : Set (CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p), Fintype.card {s : CanonicalStableRawExceptionalEdge ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno s = component} ≤ Fintype.card {token : CanonicalStableRawLeftSurplusToken ends m j k l zero hloop hjk hkl hk0 p // canonicalStableRawFullLeftTokenComponent ends m j k l zero hloop hjk hkl hk0 p hno token = component}) :
-- imply
  CanonicalStableRawCollisionTokenEmbedding ends m j k l zero hloop hjk hkl hk0 p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalStableRawCollisionTokenEmbedding_of_componentCardLE ends m j k l zero hloop hjk hkl hk0 p hno hcard


-- created on 2026-10-23
