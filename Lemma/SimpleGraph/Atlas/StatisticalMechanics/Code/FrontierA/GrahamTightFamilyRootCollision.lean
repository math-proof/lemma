import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightFamilyRootCollision
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalMaskRightAugmentedMatching_rotateSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedMatching_rotateSquare_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d e : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {q r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S)}
-- given
  (ends : I -> Sym2 W)
  (hdc : d ≠ c)
  (hec : e ≠ c)
  (hed : e ≠ d)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hfd : f d = some q)
  (hfe : f e = some r)
  (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1)
  (hrd : r.1 ∈ canonicalMaskRightImages ends m j k l zero p d.1) :
-- imply
  ∃ g : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S e g := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedMatching_rotateSquare ends m j k l zero p S c d e hdc hec hed f hf q r hfd hfe hqc hrd

/--
[canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {q r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S)}
-- given
  (ends : I -> Sym2 W)
  (hdc : d ≠ c)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hfd : f d = some q)
  (hqr : q ≠ r)
  (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1)
  (hrd : r.1 ∈ canonicalMaskRightImages ends m j k l zero p d.1) :
-- imply
  ∃ e : ↑S, e ≠ c ∧ e ≠ d ∧ f e = some r ∧ ∃ g : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S e g := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow ends m j k l zero p S c d hdc f hf q r hfd hqr hqc hrd

/--
[canonicalMaskRightAugmentedRootCollision_cut_or_reroute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedRootCollision_cut_or_reroute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {q : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hqc : q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1) :
-- imply
  (∃ d : ↑S, d ≠ c ∧ CanonicalTightOpposingRootCuts ends m j k l zero p c.1 d.1) ∨ ∃ e : ↑S, e ≠ c ∧ ∃ g : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S e g := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedRootCollision_cut_or_reroute ends m j k l zero hloop hjk hkl p S c f hf q hqc

/--
[tightFamily_rootCollisionDichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean)
-/
@[path]
private lemma tightFamily_rootCollisionDichotomy_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : c ∈ S)
  (herase : canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c) :
-- imply
  ∃ d ∈ S, d ≠ c ∧ q ∈ canonicalMaskRightImages ends m j k l zero p d ∧ CanonicalTightRootCollisionDichotomy ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.tightFamily_rootCollisionDichotomy ends m j k l zero hloop hjk hkl p S c hc herase q hqc

/--
[exists_tightFamily_allRootCollisionDichotomies_of_not_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean)
-/
@[path]
private lemma exists_tightFamily_allRootCollisionDichotomies_of_not_hall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
-- imply
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), S.Nonempty ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ ∀ c ∈ S, ∀ q, q ∈ canonicalMaskRightImages ends m j k l zero p c -> ∃ d ∈ S, d ≠ c ∧ q ∈ canonicalMaskRightImages ends m j k l zero p d ∧ CanonicalTightRootCollisionDichotomy ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_tightFamily_allRootCollisionDichotomies_of_not_hall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_tightFamily_allRootCollisionReroutes_of_not_hall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTightFamilyRootCollision.lean)
-/
@[path]
private lemma exists_tightFamily_allRootCollisionReroutes_of_not_hall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
-- imply
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), S.Nonempty ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ ∀ c : ↑S, ∃ f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f ∧ ∀ q : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), q.1 ∈ canonicalMaskRightImages ends m j k l zero p c.1 -> ((∃ d : ↑S, d ≠ c ∧ CanonicalTightOpposingRootCuts ends m j k l zero p c.1 d.1) ∨ ∃ e : ↑S, e ≠ c ∧ ∃ g : canonicalMaskRightAugmentedEquivType ends m j k l zero p S, CanonicalMaskRightAugmentedMatching ends m j k l zero p S e g) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_tightFamily_allRootCollisionReroutes_of_not_hall ends m j k l zero hloop hjk hkl hk0 p hfail


-- created on 2026-10-23
