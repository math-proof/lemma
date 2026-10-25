import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalBalancedSwap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalBalancedSwap_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r : ↑m -> Fin 4) :
-- imply
  Function.Injective fun c : ↑m -> Fin 4 => balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalBalancedSwap_injective ends m k zero r

/--
[canonicalOppositeReturn_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalOppositeReturn_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r : ↑m -> Fin 4) :
-- imply
  Function.Injective fun c : ↑m -> Fin 4 => middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalOppositeReturn_injective ends m k zero r

/--
[canonicalTransfer_oppositeReturn_eq_middleSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalTransfer_oppositeReturn_eq_middleSwap_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r c : ↑m -> Fin 4) :
-- imply
  balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) (middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) c)) = middleSwap m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransfer_oppositeReturn_eq_middleSwap ends m k zero r c

/--
[canonicalTransferWorks_oppositeReturn_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalTransferWorks_oppositeReturn_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r c : ↑m -> Fin 4) :
-- imply
  CanonicalTransferWorks ends m k zero r (middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) c)) ↔ RowsDisconnect ends m (middleSwap m c) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_oppositeReturn_iff ends m k zero r c

/--
[canonicalCollision_oppositeCorner_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalCollision_oppositeCorner_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (q r : ↑m -> Fin 4)
  (hqr : q ≠ r)
  (hcollision : middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m q k zero) (canonicalOuterTransfer ends m q k zero) q) = middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) r)) :
-- imply
  middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) q) ≠ middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m q k zero) (canonicalOuterTransfer ends m q k zero) q) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollision_oppositeCorner_ne ends m k zero q r hqr hcollision

/--
[middleSwap_canonicalQuadrangleCompletion_selfReturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma middleSwap_canonicalQuadrangleCompletion_selfReturn_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (q r : ↑m -> Fin 4) :
-- imply
  middleSwap m (canonicalQuadrangleCompletion ends m k zero q r (middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m q k zero) (canonicalOuterTransfer ends m q k zero) q))) = balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleSwap_canonicalQuadrangleCompletion_selfReturn ends m k zero q r

/--
[canonicalCollision_referenceDifference_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalCollision_referenceDifference_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (q r : ↑m -> Fin 4)
  (hqr : q ≠ r)
  (hcollision : middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m q k zero) (canonicalOuterTransfer ends m q k zero) q) = middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m r k zero) (canonicalOuterTransfer ends m r k zero) r)) :
-- imply
  canonicalQuadrangleCompletion ends m k zero q r (middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m q k zero) (canonicalOuterTransfer ends m q k zero) q)) ≠ middleSwap m (balancedSwap m (canonicalMiddleTransfer ends m q k zero) (canonicalOuterTransfer ends m q k zero) q) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCollision_referenceDifference_ne ends m k zero q r hqr hcollision

/--
[canonicalSelfTransfer_collision_oppositeWorks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalSelfTransfer_collision_oppositeWorks_eq
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
  (himage : (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p q q (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 = (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p r r (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
-- imply
  CanonicalTransferWorks ends m k zero r.1.1 q.1.1 ∧ CanonicalTransferWorks ends m k zero q.1.1 r.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfTransfer_collision_oppositeWorks ends m j k l zero hloop hjk hkl hk0 p q r himage

/--
[canonicalSelfTransfer_collision_twoCommonImages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma canonicalSelfTransfer_collision_twoCommonImages_eq
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
  ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p, q₁ ≠ q₂ ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p q ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p r ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p q ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalSelfTransfer_collision_twoCommonImages ends m j k l zero hloop hjk hkl hk0 p q r hqr himage

/--
[exists_canonicalMaskRightImage_ne_self_of_selfImage_collision](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma exists_canonicalMaskRightImage_ne_self_of_selfImage_collision_eq
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
  ∃ s : rightMaskFiber ends m j k l zero p, s ∈ canonicalMaskRightImages ends m j k l zero p q ∧ s ≠ canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p q q (canonicalTransferWorks_self hloop hjk hkl hk0 q) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightImage_ne_self_of_selfImage_collision ends m j k l zero hloop hjk hkl hk0 p q r hqr himage

/--
[card_le_canonicalMaskRightNeighborhood_of_selfImageFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalCollisionSquare.lean)
-/
@[path]
private lemma card_le_canonicalMaskRightNeighborhood_of_selfImageFiber_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (himage : ∀ c ∈ S, (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p r r (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1 = (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p c c (canonicalTransferWorks_self hloop hjk hkl hk0 c)).1.1) :
-- imply
  S.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalMaskRightNeighborhood_of_selfImageFiber ends m j k l zero hloop hjk hkl hk0 p S r himage


-- created on 2026-10-23
