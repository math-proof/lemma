import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_canonicalMaskRightImages_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma mem_canonicalMaskRightImages_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  q ∈ canonicalMaskRightImages ends m j k l zero p c ↔ ∃ r : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧ q.1.1 = balancedSwap m (canonicalMiddleTransfer ends m r.1.1 k zero) (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskRightImages_iff ends m j k l zero p c q

/--
[canonicalMaskRightImages_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightImages_nonempty_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero) :
-- imply
  (canonicalMaskRightImages ends m j k l zero p c).Nonempty := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightImages_nonempty ends m j k l zero hloop hjk hkl hk0 p c

/--
[rightMaskFiber_rowClass_zero_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma rightMaskFiber_rowClass_zero_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Function.Injective (fun q : rightMaskFiber ends m j k l zero p => rowClass m q.1.1 0) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightMaskFiber_rowClass_zero_injective ends m j k l zero p

/--
[leftMaskFiber_rowClass_zero_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma leftMaskFiber_rowClass_zero_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Function.Injective (fun c : leftMaskFiber ends m j k l zero p => rowClass m c.1.1 0) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskFiber_rowClass_zero_injective ends m j k l zero p

/--
[rowClass_zero_canonicalTransferMapOfWorks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma rowClass_zero_canonicalTransferMapOfWorks_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hworks : CanonicalTransferWorks ends m k zero a.1.1 c.1.1) :
-- imply
  rowClass m (canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p a c hworks).1.1 0 = canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_zero_canonicalTransferMapOfWorks ends m j k l zero hloop hjk hkl p a c hworks

/--
[mem_canonicalWorkingTranslatedRows_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma mem_canonicalWorkingTranslatedRows_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
  {K : Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  K ∈ canonicalWorkingTranslatedRows ends m j k l zero p c ↔ ∃ r : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧ canonicalTranslatedRow ends m k zero r.1.1 c.1.1 = K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalWorkingTranslatedRows_iff ends m j k l zero p c K

/--
[image_rowClass_zero_canonicalMaskRightImages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma image_rowClass_zero_canonicalMaskRightImages_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  (canonicalMaskRightImages ends m j k l zero p c).image (fun q => rowClass m q.1.1 0) = canonicalWorkingTranslatedRows ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.image_rowClass_zero_canonicalMaskRightImages ends m j k l zero hloop hjk hkl p c

/--
[card_canonicalMaskRightImages_eq_card_translatedRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma card_canonicalMaskRightImages_eq_card_translatedRows_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  (canonicalMaskRightImages ends m j k l zero p c).card = (canonicalWorkingTranslatedRows ends m j k l zero p c).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_canonicalMaskRightImages_eq_card_translatedRows ends m j k l zero hloop hjk hkl p c

/--
[exists_mem_canonicalMaskRightImages_iff_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_mem_canonicalMaskRightImages_iff_adjacent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p c ∧ q ∈ canonicalMaskRightImages ends m j k l zero p d) ↔ CanonicalMaskTransferAdjacent ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_mem_canonicalMaskRightImages_iff_adjacent ends m j k l zero p c d

/--
[canonicalMaskRightImages_disjoint_of_not_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightImages_disjoint_of_not_orbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcd : ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  Disjoint (canonicalMaskRightImages ends m j k l zero p c) (canonicalMaskRightImages ends m j k l zero p d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightImages_disjoint_of_not_orbit ends m j k l zero p c d hcd

/--
[mem_canonicalMaskRightNeighborhood_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma mem_canonicalMaskRightNeighborhood_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  q ∈ canonicalMaskRightNeighborhood ends m j k l zero p S ↔ ∃ c ∈ S, q ∈ canonicalMaskRightImages ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskRightNeighborhood_iff ends m j k l zero p S q

/--
[card_le_canonicalMaskRightNeighborhood_of_reference](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma card_le_canonicalMaskRightNeighborhood_of_reference_eq
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
  (hworks : ∀ c ∈ S, CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  S.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalMaskRightNeighborhood_of_reference ends m j k l zero hloop hjk hkl p S r hworks

/--
[canonicalMaskRightNeighborhood_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightNeighborhood_union_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  [DecidableEq (rightMaskFiber ends m j k l zero p)]
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalMaskRightNeighborhood ends m j k l zero p (S ∪ T) = canonicalMaskRightNeighborhood ends m j k l zero p S ∪ canonicalMaskRightNeighborhood ends m j k l zero p T := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightNeighborhood_union ends m j k l zero p S T

/--
[canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hsep : ∀ c ∈ S, ∀ d ∈ T, ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  Disjoint (canonicalMaskRightNeighborhood ends m j k l zero p S) (canonicalMaskRightNeighborhood ends m j k l zero p T) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated ends m j k l zero p S T hsep

/--
[card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  [DecidableEq (rightMaskFiber ends m j k l zero p)]
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hST : Disjoint S T)
  (hsep : ∀ c ∈ S, ∀ d ∈ T, ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d)
  (hS : S.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p S).card)
  (hT : T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card) :
-- imply
  (S ∪ T).card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p (S ∪ T)).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated ends m j k l zero p S T hST hsep hS hT

/--
[card_le_canonicalMaskRightNeighborhood_of_card_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma card_le_canonicalMaskRightNeighborhood_of_card_le_one_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hcard : S.card ≤ 1) :
-- imply
  S.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalMaskRightNeighborhood_of_card_le_one ends m j k l zero hloop hjk hkl hk0 p S hcard

/--
[canonicalMaskRightHall_iff_exists_matching](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_iff_exists_matching_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p ↔ ∃ f : leftMaskFiber ends m j k l zero p ↪ rightMaskFiber ends m j k l zero p, ∀ c, f c ∈ canonicalMaskRightImages ends m j k l zero p c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_iff_exists_matching ends m j k l zero p

/--
[GrahamFiberMinor_of_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskRightHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hhall : ∀ p : Finset I × Finset I, CanonicalMaskRightHall ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskRightHall ends m j k l zero hhall

/--
[canonicalMaskRightNeighborhood_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightNeighborhood_mono_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hST : S ⊆ T) :
-- imply
  canonicalMaskRightNeighborhood ends m j k l zero p S ⊆ canonicalMaskRightNeighborhood ends m j k l zero p T := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightNeighborhood_mono ends m j k l zero p hST

/--
[exists_other_of_erase_canonicalMaskRightNeighborhood_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_other_of_erase_canonicalMaskRightNeighborhood_eq_eq
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
  (hc : c ∈ S)
  (herase : canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c) :
-- imply
  ∃ d ∈ S, d ≠ c ∧ q ∈ canonicalMaskRightImages ends m j k l zero p d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_other_of_erase_canonicalMaskRightNeighborhood_eq ends m j k l zero p S c hc herase q hqc

/--
[exists_other_mem_canonicalWorkingTranslatedRows_of_erase_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_other_mem_canonicalWorkingTranslatedRows_of_erase_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : leftMaskFiber ends m j k l zero p}
  {K : Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : c ∈ S)
  (herase : canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hK : K ∈ canonicalWorkingTranslatedRows ends m j k l zero p c) :
-- imply
  ∃ d ∈ S, d ≠ c ∧ K ∈ canonicalWorkingTranslatedRows ends m j k l zero p d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_other_mem_canonicalWorkingTranslatedRows_of_erase_eq ends m j k l zero hloop hjk hkl p S c hc herase K hK

/--
[exists_canonicalMaskRightMatching_of_properHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightMatching_of_properHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hc : c ∈ S) :
-- imply
  ∃ f : ↑(S.erase c) ↪ rightMaskFiber ends m j k l zero p, ∀ x, f x ∈ canonicalMaskRightImages ends m j k l zero p x.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightMatching_of_properHall ends m j k l zero p S hproper c hc

/--
[exists_canonicalMaskRightNearPerfectEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightNearPerfectEquiv_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hc : c ∈ S) :
-- imply
  ∃ f : ↑(S.erase c) ≃ ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), ∀ x, (f x).1 ∈ canonicalMaskRightImages ends m j k l zero p x.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightNearPerfectEquiv ends m j k l zero p S htight hproper c hc

/--
[exists_canonicalMaskRightAugmentedEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightAugmentedEquiv_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hc : c ∈ S) :
-- imply
  ∃ f : ↑S ≃ Option ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), f ⟨c, hc⟩ = none ∧ ∀ x : ↑S, x.1 ≠ c -> ∃ q, f x = some q ∧ q.1 ∈ canonicalMaskRightImages ends m j k l zero p x.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightAugmentedEquiv ends m j k l zero p S htight hproper c hc

/--
[canonicalMaskRightAugmentedAssignedImage_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedAssignedImage_apply_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {x : ↑S}
-- given
  (ends : I -> Sym2 W)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hxc : x ≠ c) :
-- imply
  f x = some (canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf x hxc) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedAssignedImage_apply ends m j k l zero p S c f hf x hxc

/--
[canonicalMaskRightAugmentedAssignedImage_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedAssignedImage_mem_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {x : ↑S}
-- given
  (ends : I -> Sym2 W)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hxc : x ≠ c) :
-- imply
  (canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf x hxc).1 ∈ canonicalMaskRightImages ends m j k l zero p x.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedAssignedImage_mem ends m j k l zero p S c f hf x hxc

/--
[canonicalMaskRightAugmentedAssignedRows_contains](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedAssignedRows_contains_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {u : ↑S}
-- given
  (ends : I -> Sym2 W)
  (hTS : T ⊆ S)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (huT : u.1 ∈ T)
  (huc : u ≠ c) :
-- imply
  ∃ qS : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), f u = some qS ∧ qS.1 ∈ canonicalMaskRightAugmentedAssignedRows ends m j k l zero p S T hTS c f hf := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedAssignedRows_contains ends m j k l zero p S T hTS c f hf u huT huc

/--
[card_canonicalMaskRightAugmentedAssignedRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma card_canonicalMaskRightAugmentedAssignedRows_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hTS : T ⊆ S)
  (hcT : c.1 ∈ T)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f) :
-- imply
  (canonicalMaskRightAugmentedAssignedRows ends m j k l zero p S T hTS c f hf).card + 1 = T.card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_canonicalMaskRightAugmentedAssignedRows ends m j k l zero p S T hTS c hcT f hf

/--
[canonicalMaskRightAugmentedAssignedRows_subset_neighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedAssignedRows_subset_neighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S T : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hTS : T ⊆ S)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f) :
-- imply
  canonicalMaskRightAugmentedAssignedRows ends m j k l zero p S T hTS c f hf ⊆ canonicalMaskRightNeighborhood ends m j k l zero p T := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedAssignedRows_subset_neighborhood ends m j k l zero p S T hTS c f hf

/--
[canonicalMaskRightAugmentedAssignedRows_full_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedAssignedRows_full_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f) :
-- imply
  canonicalMaskRightAugmentedAssignedRows ends m j k l zero p S S Finset.Subset.rfl c f hf = canonicalMaskRightNeighborhood ends m j k l zero p S := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedAssignedRows_full_eq ends m j k l zero p S htight c f hf

/--
[canonicalMaskRightSecondRows_collision_or_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightSecondRows_collision_or_equiv_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (s : {u : ↑S // u ≠ c} -> ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
  (hne : ∀ u, s u ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2) :
-- imply
  (∃ u v, u ≠ v ∧ s u = s v) ∨ ∃ e : {u : ↑S // u ≠ c} ≃ ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), (∀ u, e u = s u) ∧ ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightSecondRows_collision_or_equiv ends m j k l zero p S c f hf s hne

/--
[canonicalMaskRightFullSecondRows_repetition_or_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightFullSecondRows_repetition_or_equiv_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hsecond : ∀ u : {u : ↑S // u ≠ c}, ∃ r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), r ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2 ∧ r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1) :
-- imply
  (∃ u v : {u : ↑S // u ≠ c}, ∃ r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), u ≠ v ∧ r ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2 ∧ r ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf v.1 v.2 ∧ r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧ r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1) ∨ ∃ e : {u : ↑S // u ≠ c} ≃ ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2 ∧ (e u).1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightFullSecondRows_repetition_or_equiv ends m j k l zero p S c f hf hsecond

/--
[canonicalMaskRightSecondRowEquiv_collisionPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightSecondRowEquiv_collisionPerm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (e : {u : ↑S // u ≠ c} ≃ ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
  (hene : ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2)
  (hemem : ∀ u, (e u).1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1) :
-- imply
  ∃ τ : Equiv.Perm {u : ↑S // u ≠ c}, (∀ u, τ u ≠ u) ∧ ∀ u, (e u).1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧ (e u).1 ∈ canonicalMaskRightImages ends m j k l zero p (τ u).1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightSecondRowEquiv_collisionPerm ends m j k l zero p S c f hf e hene hemem

/--
[canonicalMaskRightRepeatedSecondRow_threePreimages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightRepeatedSecondRow_threePreimages_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S)}
-- given
  (ends : I -> Sym2 W)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (u v : {u : ↑S // u ≠ c})
  (huv : u ≠ v)
  (hru : r ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2)
  (hrv : r ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf v.1 v.2)
  (hruMem : r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1)
  (hrvMem : r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1) :
-- imply
  ∃ w : {u : ↑S // u ≠ c}, u ≠ v ∧ w ≠ u ∧ w ≠ v ∧ r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧ r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1 ∧ r.1 ∈ canonicalMaskRightImages ends m j k l zero p w.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightRepeatedSecondRow_threePreimages ends m j k l zero p S c f hf u v r huv hru hrv hruMem hrvMem

/--
[mem_canonicalMaskRightAugmentedMatchingPairs_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma mem_canonicalMaskRightAugmentedMatchingPairs_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
  {ef : canonicalMaskRightAugmentedEquivType ends m j k l zero p S × canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W) :
-- imply
  ef ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d ↔ CanonicalMaskRightAugmentedMatching ends m j k l zero p S c ef.1 ∧ CanonicalMaskRightAugmentedMatching ends m j k l zero p S d ef.2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskRightAugmentedMatchingPairs_iff ends m j k l zero p S c d ef

/--
[canonicalMaskRightAugmentedMatchingPair_transition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedMatchingPair_transition_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
  {ef : canonicalMaskRightAugmentedEquivType ends m j k l zero p S × canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d) :
-- imply
  let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm σ c = d ∧ ∀ x : ↑S, x ≠ c -> ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedMatchingPair_transition ends m j k l zero p S c d ef hef

/--
[canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
  {ef : canonicalMaskRightAugmentedEquivType ends m j k l zero p S × canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {x : ↑S}
-- given
  (ends : I -> Sym2 W)
  (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d)
  (hxc : x ≠ c) :
-- imply
  let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧ ∀ r : rightMaskFiber ends m j k l zero p, r ≠ q -> r ∈ canonicalMaskRightImages ends m j k l zero p x.1 -> r ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 -> ∃ u v : ↑S, u ≠ c ∧ v ≠ d ∧ u ≠ x ∧ v ≠ σ x ∧ σ u = v ∧ r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧ r ∈ canonicalMaskRightImages ends m j k l zero p v.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement ends m j k l zero p S c d ef hef x hxc

/--
[exists_canonicalMaskRightNeighbor_not_mem_of_properHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightNeighbor_not_mem_of_properHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {T : Finset (leftMaskFiber ends m j k l zero p)}
  {R : Finset (rightMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hTS : T ⊂ S)
  (hcard : R.card < T.card) :
-- imply
  ∃ x ∈ T, ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q ∉ R := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightNeighbor_not_mem_of_properHall ends m j k l zero p S hproper T hTS R hcard

/--
[exists_canonicalMaskRightNeighbor_ne_pair_of_properHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightNeighbor_ne_pair_of_properHall_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {T : Finset (leftMaskFiber ends m j k l zero p)}
  {q r : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hTS : T ⊂ S)
  (hcard : 2 < T.card) :
-- imply
  ∃ x ∈ T, ∃ s : rightMaskFiber ends m j k l zero p, s ∈ canonicalMaskRightImages ends m j k l zero p x ∧ s ≠ q ∧ s ≠ r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightNeighbor_ne_pair_of_properHall ends m j k l zero p S hproper T hTS hcard q r

/--
[canonicalMaskRightExposure_terminal_or_escapes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightExposure_terminal_or_escapes_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {T : Finset (leftMaskFiber ends m j k l zero p)}
  {R : Finset (rightMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hTS : T ⊆ S)
  (hR : R ⊆ canonicalMaskRightNeighborhood ends m j k l zero p T)
  (hdef : R.card + 1 = T.card) :
-- imply
  (T = S ∧ R = canonicalMaskRightNeighborhood ends m j k l zero p S) ∨ ∃ x ∈ T, ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q ∉ R := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightExposure_terminal_or_escapes ends m j k l zero p S htight hproper T hTS R hR hdef

/--
[exists_canonicalMaskRightAugmentedMatching_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightAugmentedMatching_escape_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {T : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {R : Finset (rightMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hTS : T ⊂ S)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hcard : R.card < T.card)
  (hassigned : ∀ u : ↑S, u.1 ∈ T -> u ≠ c -> ∃ qS : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), f u = some qS ∧ qS.1 ∈ R) :
-- imply
  ∃ x ∈ T, ∃ qS : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), qS.1 ∈ canonicalMaskRightImages ends m j k l zero p x ∧ qS.1 ∉ R ∧ ∃ u : ↑S, f u = some qS ∧ u.1 ∉ T ∧ (S \ insert u.1 T).card < (S \ T).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightAugmentedMatching_escape ends m j k l zero p S hproper T hTS c f hf R hcard hassigned

/--
[exists_canonicalMaskRightAugmentedMatching_strictExposure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightAugmentedMatching_strictExposure_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {T : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hTS : T ⊂ S)
  (hcT : c.1 ∈ T)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f) :
-- imply
  ∃ x ∈ T, ∃ qS : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), qS.1 ∈ canonicalMaskRightImages ends m j k l zero p x ∧ qS.1 ∉ canonicalMaskRightAugmentedAssignedRows ends m j k l zero p S T hTS.1 c f hf ∧ ∃ u : ↑S, f u = some qS ∧ u.1 ∉ T ∧ (S \ insert u.1 T).card < (S \ T).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightAugmentedMatching_strictExposure ends m j k l zero p S hproper T hTS c hcT f hf

/--
[canonicalMaskRightAugmentedExposureClosed_eq_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedExposureClosed_eq_full_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {T : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hTS : T ⊆ S)
  (hcT : c.1 ∈ T)
  (hclosed : ∀ x ∈ T, ∀ u : ↑S, ∀ huc : u ≠ c, (canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u huc).1 ∈ canonicalMaskRightImages ends m j k l zero p x -> u.1 ∈ T) :
-- imply
  T = S := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedExposureClosed_eq_full ends m j k l zero p S hproper c f hf T hTS hcT hclosed

/--
[exists_minimal_canonicalMaskRightAugmentedMatchingPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_minimal_canonicalMaskRightAugmentedMatchingPair_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card) :
-- imply
  ∃ ef ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d, ∀ gh ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d, canonicalPermMovedCard (ef.1.trans ef.2.symm : Equiv.Perm ↑S) ≤ canonicalPermMovedCard (gh.1.trans gh.2.symm : Equiv.Perm ↑S) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_minimal_canonicalMaskRightAugmentedMatchingPair ends m j k l zero p S htight hproper c d

/--
[exists_minimal_canonicalMaskRightPair_with_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_minimal_canonicalMaskRightPair_with_displacement_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card) :
-- imply
  ∃ ef ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d, (∀ gh ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d, canonicalPermMovedCard (ef.1.trans ef.2.symm : Equiv.Perm ↑S) ≤ canonicalPermMovedCard (gh.1.trans gh.2.symm : Equiv.Perm ↑S)) ∧ CanonicalMaskRightSecondCommonDisplacement ends m j k l zero p S c d ef := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_minimal_canonicalMaskRightPair_with_displacement ends m j k l zero p S htight hproper c d

/--
[exists_canonicalMaskRightAlternatingPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskRightAlternatingPerm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hc : c ∈ S)
  (hd : d ∈ S) :
-- imply
  ∃ σ : Equiv.Perm ↑S, σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧ ∀ x : ↑S, x.1 ≠ c -> ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskRightAlternatingPerm ends m j k l zero p S htight hproper c d hc hd

/--
[exists_canonicalMaskTransferAdjacentPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalMaskTransferAdjacentPerm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hc : c ∈ S)
  (hd : d ∈ S)
  (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d) :
-- imply
  ∃ σ : Equiv.Perm ↑S, σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧ ∀ x : ↑S, CanonicalMaskTransferAdjacent ends m j k l zero p x.1 (σ x).1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalMaskTransferAdjacentPerm ends m j k l zero p S htight hproper c d hc hd hcd

/--
[exists_canonicalTranslatedRowPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalTranslatedRowPerm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card)
  (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
  (hc : c ∈ S)
  (hd : d ∈ S)
  (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d) :
-- imply
  ∃ σ : Equiv.Perm ↑S, σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧ ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalTranslatedRowPerm ends m j k l zero hloop hjk hkl p S htight hproper c d hc hd hcd

/--
[symmDiffFold_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma symmDiffFold_pair_eq
  [Fintype I]
  [DecidableEq I]
  {s : Finset A}
-- given
  (f g : A -> Finset I) :
-- imply
  symmDiffFold s (fun x => f x ∆ g x) = symmDiffFold s f ∆ symmDiffFold s g := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiffFold_pair s f g

/--
[symmDiffFold_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma symmDiffFold_equiv_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {e : Equiv.Perm A}
-- given
  (f : A -> Finset I) :
-- imply
  symmDiffFold Finset.univ (fun x => f (e x)) = symmDiffFold Finset.univ f := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiffFold_equiv e f

/--
[symmDiffFold_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma symmDiffFold_const_eq
  [Fintype I]
  [DecidableEq I]
  {s : Finset A}
  {C : Finset I} :
-- imply
  symmDiffFold s (fun _ => C) = if s.card % 2 = 0 then ∅ else C := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiffFold_const s C

/--
[sources_symmDiffFold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma sources_symmDiffFold_eq
  [Fintype I]
  [DecidableEq I]
  {s : Finset A}
-- given
  (ends : I -> Sym2 W)
  (f : A -> Finset I) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) = symmDiffFold s (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_symmDiffFold ends s f

/--
[sources_symmDiffFold_of_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma sources_symmDiffFold_of_constant_eq
  [Fintype I]
  [DecidableEq I]
  {s : Finset A}
  {C : Finset W}
-- given
  (ends : I -> Sym2 W)
  (f : A -> Finset I)
  (hsrc : ∀ a ∈ s, StatMech.Sharpness.RandomCurrent.sources ends (f a) = C) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) = if s.card % 2 = 0 then ∅ else C := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_symmDiffFold_of_constant ends s f C hsrc

/--
[sources_symmDiffFold_rightMaskRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma sources_symmDiffFold_rightMaskRows_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {s : Finset A}
-- given
  (ends : I -> Sym2 W)
  (Q : A -> rightMaskFiber ends m j k l zero p) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s (fun x => rowClass m (Q x).1.1 0)) = if s.card % 2 = 0 then ∅ else {j, k} ∆ {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_symmDiffFold_rightMaskRows ends m j k l zero p s Q

/--
[symmDiffFold_endpointCancellation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma symmDiffFold_endpointCancellation_eq
  [Fintype I]
  [DecidableEq I]
  [Fintype A]
  {σ : Equiv.Perm A}
-- given
  (Q R : A -> Finset I) :
-- imply
  symmDiffFold Finset.univ (fun x => Q x ∆ R x ∆ R (σ x)) = symmDiffFold Finset.univ Q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiffFold_endpointCancellation Q R σ

/--
[exists_referenceTransferFold_eq_of_translatedRowPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_referenceTransferFold_eq_of_translatedRowPerm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {σ : Equiv.Perm ↑S}
-- given
  (ends : I -> Sym2 W)
  (hrows : ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1) :
-- imply
  ∃ a b : ↑S -> leftMaskFiber ends m j k l zero p, (∀ x, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1) k zero) ∧ (∀ x, canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero (b x).1.1 (σ x).1.1.1) ∧ symmDiffFold Finset.univ (fun x => canonicalTransferUnion ends m k zero (a x).1.1) = symmDiffFold Finset.univ (fun x => canonicalTransferUnion ends m k zero (b x).1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_referenceTransferFold_eq_of_translatedRowPerm ends m j k l zero p S σ hrows

/--
[canonicalTranslatedRow_opposite_eq_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_opposite_eq_of_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b x y : ↑m -> Fin 4)
  (hxy : canonicalTranslatedRow ends m k zero a x = canonicalTranslatedRow ends m k zero b y) :
-- imply
  canonicalTranslatedRow ends m k zero b x = canonicalTranslatedRow ends m k zero a y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_opposite_eq_of_eq ends m k zero a b x y hxy

/--
[canonicalTranslatedRow_opposite_rootCutBranches_iff_of_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_opposite_rootCutBranches_iff_of_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b x y : ↑m -> Fin 4)
  (hxy : canonicalTranslatedRow ends m k zero a x = canonicalTranslatedRow ends m k zero b y) :
-- imply
  let Kx := canonicalTranslatedRow ends m k zero b x let Ky := canonicalTranslatedRow ends m k zero a y ((StatMech.Sharpness.RandomCurrent.connK ends Kx k zero ∧ edgeComponent ends Kx zero = edgeComponent ends Kx k) ↔ (StatMech.Sharpness.RandomCurrent.connK ends Ky k zero ∧ edgeComponent ends Ky zero = edgeComponent ends Ky k)) ∧ ((StatMech.Sharpness.RandomCurrent.connK ends (m \ Kx) k zero ∧ edgeComponent ends (m \ Kx) zero = edgeComponent ends (m \ Kx) k) ↔ (StatMech.Sharpness.RandomCurrent.connK ends (m \ Ky) k zero ∧ edgeComponent ends (m \ Ky) zero = edgeComponent ends (m \ Ky) k)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_opposite_rootCutBranches_iff_of_eq ends m k zero a b x y hxy

/--
[canonicalTransferWorks_opposite_iff_of_translatedRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTransferWorks_opposite_iff_of_translatedRow_eq_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b x y : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hxy : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 = canonicalTranslatedRow ends m k zero b.1.1 y.1.1) :
-- imply
  CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ↔ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_opposite_iff_of_translatedRow_eq hloop hjk hkl a b x y hxy

/--
[exists_two_common_canonicalMaskRightImages_of_collisionSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_two_common_canonicalMaskRightImages_of_collisionSquare_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b x y : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hxyne : x ≠ y)
  (hax : CanonicalTransferWorks ends m k zero a.1.1 x.1.1)
  (hxy : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 = canonicalTranslatedRow ends m k zero b.1.1 y.1.1)
  (hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1) :
-- imply
  ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p, q₁ ≠ q₂ ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_two_common_canonicalMaskRightImages_of_collisionSquare hloop hjk hkl a b x y hxyne hax hxy hbx

/--
[canonicalTranslatedRow_subset_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_subset_m_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  canonicalTranslatedRow ends m k zero r.1.1 c.1.1 ⊆ m := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_subset_m hloop hjk hkl r c

/--
[canonicalTranslatedRow_boundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_boundaries_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  StatMech.Sharpness.RandomCurrent.sources ends (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) = {j, k} ∆ {k, l} ∧ StatMech.Sharpness.RandomCurrent.sources ends (m \ canonicalTranslatedRow ends m k zero r.1.1 c.1.1) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_boundaries hloop hjk hkl r c

/--
[canonicalTranslatedRow_sourcePair_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_sourcePair_connected_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hjl : j ≠ l) :
-- imply
  StatMech.Sharpness.RandomCurrent.connK ends (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) j l := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_sourcePair_connected hloop hjk hkl hjl r c

/--
[canonicalTranslatedRow_conn_source_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_conn_source_iff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero u : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hjl : j ≠ l) :
-- imply
  StatMech.Sharpness.RandomCurrent.connK ends (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) u j ↔ StatMech.Sharpness.RandomCurrent.connK ends (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) u l := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_conn_source_iff hloop hjk hkl hjl r c

/--
[canonicalTranslatedRow_component_sources_empty_or_full](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_component_sources_empty_or_full_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero u : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1 let A := {j, k} ∆ {k, l} StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends K u) = ∅ ∨ StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends K u) = A := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_component_sources_empty_or_full hloop hjk hkl r c

/--
[canonicalTranslatedRow_rootComponent_boundaryCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTranslatedRow_rootComponent_boundaryCertificate_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcut : CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1) :
-- imply
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1 let A := {j, k} ∆ {k, l} StatMech.Sharpness.RandomCurrent.sources ends K = A ∧ StatMech.Sharpness.RandomCurrent.sources ends (m \ K) = ∅ ∧ ((StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧ edgeComponent ends K zero = edgeComponent ends K k ∧ ((StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends K zero) = ∅ ∧ StatMech.Sharpness.RandomCurrent.sources ends (K \ edgeComponent ends K zero) = A) ∨ (StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends K zero) = A ∧ StatMech.Sharpness.RandomCurrent.sources ends (K \ edgeComponent ends K zero) = ∅))) ∨ (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧ edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k ∧ StatMech.Sharpness.RandomCurrent.sources ends (edgeComponent ends (m \ K) zero) = ∅ ∧ StatMech.Sharpness.RandomCurrent.sources ends ((m \ K) \ edgeComponent ends (m \ K) zero) = ∅)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_rootComponent_boundaryCertificate hloop hjk hkl r c hcut

/--
[canonicalTransferWorks_failed_translatedRow_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTransferWorks_failed_translatedRow_component_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1 (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧ edgeComponent ends K zero = edgeComponent ends K k) ∨ (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧ edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_failed_translatedRow_component hloop hjk hkl r c hbad

/--
[canonicalTransferWorks_failed_rootComponentCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalTransferWorks_failed_rootComponentCut_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_failed_rootComponentCut hloop hjk hkl r c hbad

/--
[canonicalMaskRightAugmentedExposure_failedOpposite_or_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedExposure_failedOpposite_or_square_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {x u : ↑S}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (huc : u ≠ c)
  (hxu : x ≠ u)
  (hshare : (canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u huc).1 ∈ canonicalMaskRightImages ends m j k l zero p x.1) :
-- imply
  ∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 u.1.1.1 ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero b.1.1 u.1.1.1 ∧ (¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1 ∨ ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p, q₁ ≠ q₂ ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p u.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedExposure_failedOpposite_or_square hloop hjk hkl S c f hf x u huc hxu hshare

/--
[canonicalMaskRightAugmentedExposure_componentCut_or_square](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightAugmentedExposure_componentCut_or_square_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {x u : ↑S}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (huc : u ≠ c)
  (hxu : x ≠ u)
  (hshare : (canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u huc).1 ∈ canonicalMaskRightImages ends m j k l zero p x.1) :
-- imply
  ∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 u.1.1.1 ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero b.1.1 u.1.1.1 ∧ (((StatMech.Sharpness.RandomCurrent.connK ends (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k zero ∧ edgeComponent ends (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) zero = edgeComponent ends (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k) ∨ (StatMech.Sharpness.RandomCurrent.connK ends (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k zero ∧ edgeComponent ends (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) zero = edgeComponent ends (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k)) ∨ ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p, q₁ ≠ q₂ ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p u.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightAugmentedExposure_componentCut_or_square hloop hjk hkl S c f hf x u huc hxu hshare

/--
[canonicalMaskRightFullExposure_cut_or_secondRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightFullExposure_cut_or_secondRow_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (u : {u : ↑S // u ≠ c}) :
-- imply
  (∃ r x : leftMaskFiber ends m j k l zero p, x ∈ S ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 x.1.1) ∨ ∃ s : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), s ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2 ∧ s.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightFullExposure_cut_or_secondRow hloop hjk hkl S herase c f hf u

/--
[canonicalMaskRightFullExposure_secondRows_of_noCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightFullExposure_secondRows_of_noCut_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c : ↑S}
  {f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) = canonicalMaskRightNeighborhood ends m j k l zero p S)
  (hf : CanonicalMaskRightAugmentedMatching ends m j k l zero p S c f)
  (hnoCut : ∀ r x : leftMaskFiber ends m j k l zero p, x ∈ S -> ¬ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 x.1.1) :
-- imply
  ∀ u : {u : ↑S // u ≠ c}, ∃ s : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S), s ≠ canonicalMaskRightAugmentedAssignedImage ends m j k l zero p S c f hf u.1 u.2 ∧ s.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightFullExposure_secondRows_of_noCut hloop hjk hkl S herase c f hf hnoCut

/--
[canonicalMaskRightMatchingPair_failedOpposite_or_expands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightMatchingPair_failedOpposite_or_expands_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {c d : ↑S}
  {ef : canonicalMaskRightAugmentedEquivType ends m j k l zero p S × canonicalMaskRightAugmentedEquivType ends m j k l zero p S}
  {x : ↑S}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs ends m j k l zero p S c d)
  (hxc : x ≠ c)
  (hmove : x ≠ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) x) :
-- imply
  ∃ q : rightMaskFiber ends m j k l zero p, q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ q ∈ canonicalMaskRightImages ends m j k l zero p ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1 ∧ ∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1.1.1 ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero b.1.1 ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1.1.1 ∧ (¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1 ∨ ∃ r : rightMaskFiber ends m j k l zero p, r ≠ q ∧ r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧ r ∈ canonicalMaskRightImages ends m j k l zero p ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1 ∧ ∃ u v : ↑S, u ≠ c ∧ v ≠ d ∧ u ≠ x ∧ v ≠ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) x ∧ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) u = v ∧ r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧ r ∈ canonicalMaskRightImages ends m j k l zero p v.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightMatchingPair_failedOpposite_or_expands hloop hjk hkl S c d ef hef x hxc hmove

/--
[exists_tight_canonicalMaskRightHall_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_tight_canonicalMaskRightHall_obstruction_eq
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
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), S.Nonempty ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ (∀ c ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) = canonicalMaskRightNeighborhood ends m j k l zero p S) ∧ (∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card) ∧ (∀ c ∈ S, ∀ d ∈ S, CanonicalMaskTransferOrbit ends m j k l zero p c d) ∧ (∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧ CanonicalMaskTransferAdjacent ends m j k l zero p c d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_tight_canonicalMaskRightHall_obstruction ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall_eq
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
  ∃ (S : Finset (leftMaskFiber ends m j k l zero p)) (a r c : leftMaskFiber ends m j k l zero p), S.Nonempty ∧ a ∈ S ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ (∀ x ∈ S, canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) = canonicalMaskRightNeighborhood ends m j k l zero p S) ∧ (∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S -> T.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p T).card) ∧ (∀ d ∈ S, CanonicalMaskTransferOrbit ends m j k l zero p a d) ∧ CanonicalMaskTransferOrbit ends m j k l zero p a r ∧ (∀ t : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferOrbit ends m j k l zero p a t -> (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤ (canonicalMaskOrbitCoverage ends m j k l zero p r).card) ∧ c ∈ S ∧ c ∈ canonicalMaskOrbitCoverage ends m j k l zero p c ∧ c ∉ canonicalMaskOrbitCoverage ends m j k l zero p r ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_maximalOrbitCoverage_quadrangleDichotomy_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_maximalOrbitCoverage_quadrangleDichotomy_of_not_canonicalMaskRightHall_eq
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
  ∃ (S : Finset (leftMaskFiber ends m j k l zero p)) (a r c : leftMaskFiber ends m j k l zero p), S.Nonempty ∧ a ∈ S ∧ (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ (∀ d ∈ S, CanonicalMaskTransferOrbit ends m j k l zero p a d) ∧ CanonicalMaskTransferOrbit ends m j k l zero p a r ∧ (∀ t : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferOrbit ends m j k l zero p a t -> (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤ (canonicalMaskOrbitCoverage ends m j k l zero p r).card) ∧ c ∈ S ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 ∧ ((∃ d : leftMaskFiber ends m j k l zero p, d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧ d ∉ canonicalMaskOrbitCoverage ends m j k l zero p c) ∨ (c ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p c r ∧ ∃ d : leftMaskFiber ends m j k l zero p, d ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p r c)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_maximalOrbitCoverage_quadrangleDichotomy_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[mem_canonicalTransferUnion_iff_row_componentComplements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma mem_canonicalTransferUnion_iff_row_componentComplements_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
  {e : I}
  {u : W}
-- given
  (hem : e ∈ m)
  (hu : u ∈ ends e) :
-- imply
  e ∈ canonicalTransferUnion ends m k zero c.1.1 ↔ ((e ∈ rowClass m c.1.1 0 ∧ u ∉ StatMech.FrontierA.grahamComponentComplement ends (rowClass m c.1.1 0) zero) ∨ (e ∉ rowClass m c.1.1 0 ∧ u ∉ StatMech.FrontierA.grahamComponentComplement ends (m \ rowClass m c.1.1 0) k)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalTransferUnion_iff_row_componentComplements c hem hu

/--
[canonicalMaskNormalFiberComplete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskNormalFiberComplete_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  CanonicalMaskNormalFiberComplete ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskNormalFiberComplete ends m j k l zero hloop hjk hkl p

/--
[canonicalNormalRows_ne_of_not_canonicalTransferWorks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalNormalRows_ne_of_not_canonicalTransferWorks_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  canonicalNormalRow ends m k zero r.1.1 ≠ canonicalNormalRow ends m k zero c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRows_ne_of_not_canonicalTransferWorks hloop hjk hkl r c hbad

/--
[canonicalNormalRows_ne_of_rootComponentCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalNormalRows_ne_of_rootComponentCut_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcut : CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1) :
-- imply
  canonicalNormalRow ends m k zero r.1.1 ≠ canonicalNormalRow ends m k zero c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRows_ne_of_rootComponentCut hloop hjk hkl r c hcut

/--
[card_le_canonicalMaskRightNeighborhood_of_normalFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma card_le_canonicalMaskRightNeighborhood_of_normalFiber_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hnormal : ∀ c ∈ S, canonicalNormalRow ends m k zero r.1.1 = canonicalNormalRow ends m k zero c.1.1) :
-- imply
  S.card ≤ (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_le_canonicalMaskRightNeighborhood_of_normalFiber hloop hjk hkl S r hnormal

/--
[canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
  (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b) :
-- imply
  CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p a b c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate hloop hjk hkl a b c hab hc

/--
[canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {x y : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hxyne : x ≠ y)
  (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y) :
-- imply
  (∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1 = canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero b.1.1 x.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero a.1.1 y.1.1) ∨ ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p, q₁ ≠ q₂ ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages hloop hjk hkl x y hxyne hxy

/--
[exists_collisionReferenceDifference_at_adjacentFailedCutCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_collisionReferenceDifference_at_adjacentFailedCutCrossing_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r x y : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y)
  (hrx : CanonicalTransferWorks ends m k zero r.1.1 x.1.1)
  (hry : ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1) :
-- imply
  ∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1 = canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧ ∃ e : I, e ∈ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 ∧ let Kx := canonicalTranslatedRow ends m k zero r.1.1 x.1.1 let Ky := canonicalTranslatedRow ends m k zero r.1.1 y.1.1 ((e ∈ Ky \ Kx ∧ ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧ u ∉ StatMech.FrontierA.grahamComponentComplement ends Kx k ∧ v ∈ StatMech.FrontierA.grahamComponentComplement ends Kx k) ∨ (e ∈ (m \ Ky) \ (m \ Kx) ∧ ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧ u ∉ StatMech.FrontierA.grahamComponentComplement ends (m \ Kx) k ∧ v ∈ StatMech.FrontierA.grahamComponentComplement ends (m \ Kx) k)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_collisionReferenceDifference_at_adjacentFailedCutCrossing hloop hjk hkl r x y hxy hrx hry

/--
[exists_rootIncident_transferDifference_of_equalNormal_failed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_rootIncident_transferDifference_of_equalNormal_failed_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hnormal : canonicalNormalRow ends m k zero r.1.1 = canonicalNormalRow ends m k zero c.1.1)
  (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  ∃ e : I, e ∈ canonicalTransferUnion ends m k zero r.1.1 ∆ canonicalTransferUnion ends m k zero c.1.1 ∧ let N := canonicalNormalRow ends m k zero r.1.1 let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1 ((e ∈ K \ N ∧ zero ∈ ends e) ∨ (e ∈ (m \ K) \ (m \ N) ∧ k ∈ ends e)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_rootIncident_transferDifference_of_equalNormal_failed hloop hjk hkl hk0 r c hnormal hbad

/--
[canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates_eq
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
  (hprop : CanonicalMaskAdjacentWorksPropagates ends m j k l zero p) :
-- imply
  CanonicalMaskTransferOrbitInternallyComplete ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates ends m j k l zero hloop hjk hkl hk0 p hprop

/--
[canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hinvariant : CanonicalMaskAdjacentNormalInvariant ends m j k l zero p)
  (hcomplete : CanonicalMaskNormalFiberComplete ends m j k l zero p) :
-- imply
  CanonicalMaskTransferOrbitInternallyComplete ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry ends m j k l zero p hinvariant hcomplete

/--
[exists_adjacent_normalRow_ne_of_orbit_normalRow_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_adjacent_normalRow_ne_of_orbit_normalRow_ne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c)
  (hne : canonicalNormalRow ends m k zero r.1.1 ≠ canonicalNormalRow ends m k zero c.1.1) :
-- imply
  ∃ x y : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferOrbit ends m j k l zero p r x ∧ CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧ canonicalNormalRow ends m k zero x.1.1 ≠ canonicalNormalRow ends m k zero y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_adjacent_normalRow_ne_of_orbit_normalRow_ne ends m j k l zero p r c hrc hne

/--
[exists_adjacent_works_failed_of_orbit_failed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_adjacent_works_failed_of_orbit_failed_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hself : CanonicalTransferWorks ends m k zero r.1.1 r.1.1)
  (hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c)
  (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
-- imply
  ∃ x y : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferOrbit ends m j k l zero p r x ∧ CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧ CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_adjacent_works_failed_of_orbit_failed ends m j k l zero p r c hself hrc hbad

/--
[canonicalMaskRightHall_of_orbitInternallyComplete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_orbitInternallyComplete_eq
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
  (hcomplete : CanonicalMaskTransferOrbitInternallyComplete ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_orbitInternallyComplete ends m j k l zero hloop hjk hkl p hcomplete

/--
[canonicalMaskRightHall_of_adjacentWorksPropagates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_adjacentWorksPropagates_eq
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
  (hprop : CanonicalMaskAdjacentWorksPropagates ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_adjacentWorksPropagates ends m j k l zero hloop hjk hkl hk0 p hprop

/--
[canonicalMaskRightHall_of_normalGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_normalGeometry_eq
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
  (hinvariant : CanonicalMaskAdjacentNormalInvariant ends m j k l zero p)
  (hcomplete : CanonicalMaskNormalFiberComplete ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_normalGeometry ends m j k l zero hloop hjk hkl p hinvariant hcomplete

/--
[GrahamFiberMinor_of_orbitInternallyComplete](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_orbitInternallyComplete_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hcomplete : ∀ p : Finset I × Finset I, CanonicalMaskTransferOrbitInternallyComplete ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_orbitInternallyComplete ends m j k l zero hloop hjk hkl hcomplete

/--
[GrahamFiberMinor_of_adjacentWorksPropagates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_adjacentWorksPropagates_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hprop : ∀ p : Finset I × Finset I, CanonicalMaskAdjacentWorksPropagates ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_adjacentWorksPropagates ends m j k l zero hloop hjk hkl hk0 hprop

/--
[GrahamFiberMinor_of_normalGeometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_normalGeometry_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hinvariant : ∀ p : Finset I × Finset I, CanonicalMaskAdjacentNormalInvariant ends m j k l zero p)
  (hcomplete : ∀ p : Finset I × Finset I, CanonicalMaskNormalFiberComplete ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_normalGeometry ends m j k l zero hloop hjk hkl hinvariant hcomplete

/--
[exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall_eq
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
  ∃ r c : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferOrbit ends m j k l zero p r c ∧ ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_normalGeometry_obstruction_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_normalGeometry_obstruction_of_not_canonicalMaskRightHall_eq
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
  (∃ x y : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧ canonicalNormalRow ends m k zero x.1.1 ≠ canonicalNormalRow ends m k zero y.1.1) ∨ ∃ r c : leftMaskFiber ends m j k l zero p, canonicalNormalRow ends m k zero r.1.1 = canonicalNormalRow ends m k zero c.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_normalGeometry_obstruction_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_adjacent_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_adjacent_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall_eq
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
  ∃ r x y : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferOrbit ends m j k l zero p r x ∧ CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧ CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_adjacent_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall_eq
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
  ∃ r x y : leftMaskFiber ends m j k l zero p, CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧ CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 y.1.1 ∧ ((∃ d : leftMaskFiber ends m j k l zero p, d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧ d ∉ canonicalMaskOrbitCoverage ends m j k l zero p y) ∨ (y ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p y r ∧ ∃ d : leftMaskFiber ends m j k l zero p, d ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p r y)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_maximalCoverage_adjacentBoundary_opposingCertificates_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_maximalCoverage_adjacentBoundary_opposingCertificates_of_not_canonicalMaskRightHall_eq
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
  ∃ r x y : leftMaskFiber ends m j k l zero p, CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧ CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 y.1.1 ∧ ((∃ d : leftMaskFiber ends m j k l zero p, d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧ d ∉ canonicalMaskOrbitCoverage ends m j k l zero p y) ∨ ∃ d : leftMaskFiber ends m j k l zero p, y ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p y r ∧ d ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p r y ∧ CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p y r y ∧ CanonicalCoverageExclusiveBoundaryCertificate ends m j k l zero p r y d) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_maximalCoverage_adjacentBoundary_opposingCertificates_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_maximalCoverage_adjacentBoundary_oppositeRootCuts_or_twoCommonImages_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_maximalCoverage_adjacentBoundary_oppositeRootCuts_or_twoCommonImages_of_not_canonicalMaskRightHall_eq
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
  ∃ r x y : leftMaskFiber ends m j k l zero p, CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧ CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 y.1.1 ∧ ((∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1 = canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero b.1.1 x.1.1 ∧ CanonicalTranslatedRowRootComponentCut ends m k zero a.1.1 y.1.1) ∨ ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p, q₁ ≠ q₂ ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q₂ ∈ canonicalMaskRightImages ends m j k l zero p y) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_maximalCoverage_adjacentBoundary_oppositeRootCuts_or_twoCommonImages_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hSne : S.Nonempty)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card) :
-- imply
  ∃ r ∈ S, ∃ c ∈ S, CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood ends m j k l zero hloop hjk hkl p S hSne htight

/--
[exists_distinctNormalRows_of_tight_canonicalMaskRightNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_distinctNormalRows_of_tight_canonicalMaskRightNeighborhood_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hSne : S.Nonempty)
  (htight : (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card) :
-- imply
  ∃ r ∈ S, ∃ c ∈ S, canonicalNormalRow ends m k zero r.1.1 ≠ canonicalNormalRow ends m k zero c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_distinctNormalRows_of_tight_canonicalMaskRightNeighborhood ends m j k l zero hloop hjk hkl p S hSne htight

/--
[exists_rootComponentCut_of_not_canonicalMaskRightHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_rootComponentCut_of_not_canonicalMaskRightHall_eq
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
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), ∃ r ∈ S, ∃ c ∈ S, CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_rootComponentCut_of_not_canonicalMaskRightHall ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[canonicalMaskRightHall_of_no_rootComponentCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_no_rootComponentCut_eq
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
  (hno : ∀ r c : leftMaskFiber ends m j k l zero p, ¬ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_no_rootComponentCut ends m j k l zero hloop hjk hkl hk0 p hno

/--
[mem_canonicalMaskRightRestrictedCoverage_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma mem_canonicalMaskRightRestrictedCoverage_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  c ∈ canonicalMaskRightRestrictedCoverage ends m j k l zero p S r ↔ c ∈ S ∧ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskRightRestrictedCoverage_iff ends m j k l zero p S r c

/--
[canonicalMaskRightRestrictedCoverage_eq_inter_orbitCoverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightRestrictedCoverage_eq_inter_orbitCoverage_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  [DecidableEq (leftMaskFiber ends m j k l zero p)]
  {S : Finset (leftMaskFiber ends m j k l zero p)}
  {r : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (horbit : ∀ d ∈ S, CanonicalMaskTransferOrbit ends m j k l zero p r d) :
-- imply
  canonicalMaskRightRestrictedCoverage ends m j k l zero p S r = S ∩ canonicalMaskOrbitCoverage ends m j k l zero p r := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightRestrictedCoverage_eq_inter_orbitCoverage ends m j k l zero p S r horbit

/--
[canonicalMaskRightTightRootCutCoverageMerge_of_excluded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightTightRootCutCoverageMerge_of_excluded_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hno : CanonicalMaskRightTightRootCutExcluded ends m j k l zero p) :
-- imply
  CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightTightRootCutCoverageMerge_of_excluded ends m j k l zero p hno

/--
[canonicalMaskRightHall_of_tightRootCutCoverageMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_tightRootCutCoverageMerge_eq
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
  (hmerge : CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_tightRootCutCoverageMerge ends m j k l zero hloop hjk hkl hk0 p hmerge

/--
[canonicalMaskRightHall_of_tightRootCutExcluded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma canonicalMaskRightHall_of_tightRootCutExcluded_eq
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
  (hno : CanonicalMaskRightTightRootCutExcluded ends m j k l zero p) :
-- imply
  CanonicalMaskRightHall ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightHall_of_tightRootCutExcluded ends m j k l zero hloop hjk hkl hk0 p hno

/--
[GrahamFiberMinor_of_no_canonicalTranslatedRowRootComponentCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_no_canonicalTranslatedRowRootComponentCut_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : ∀ (p : Finset I × Finset I) (r c : leftMaskFiber ends m j k l zero p), ¬ CanonicalTranslatedRowRootComponentCut ends m k zero r.1.1 c.1.1) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_no_canonicalTranslatedRowRootComponentCut ends m j k l zero hloop hjk hkl hk0 hno

/--
[GrahamFiberMinor_of_tightRootCutCoverageMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_tightRootCutCoverageMerge_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hmerge : ∀ p : Finset I × Finset I, CanonicalMaskRightTightRootCutCoverageMerge ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_tightRootCutCoverageMerge ends m j k l zero hloop hjk hkl hk0 hmerge

/--
[GrahamFiberMinor_of_tightRootCutExcluded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_tightRootCutExcluded_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hno : ∀ p : Finset I × Finset I, CanonicalMaskRightTightRootCutExcluded ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_tightRootCutExcluded ends m j k l zero hloop hjk hkl hk0 hno

/--
[exists_canonicalTranslatedRowCycle_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalTranslatedRowCycle_obstruction_eq
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
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 = S.card ∧ ∃ c d : ↑S, c ≠ d ∧ ∃ σ : Equiv.Perm ↑S, σ c = d ∧ ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧ canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalTranslatedRowCycle_obstruction ends m j k l zero hloop hjk hkl hk0 p hfail

/--
[exists_canonicalTransferFoldCycle_obstruction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferMatching.lean)
-/
@[path]
private lemma exists_canonicalTransferFoldCycle_obstruction_eq
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
  ∃ S : Finset (leftMaskFiber ends m j k l zero p), ∃ σ : Equiv.Perm ↑S, σ ≠ Equiv.refl ↑S ∧ ∃ a b : ↑S -> leftMaskFiber ends m j k l zero p, (∀ x, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1) k zero) ∧ (∀ x, canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1 = canonicalTranslatedRow ends m k zero (b x).1.1 (σ x).1.1.1) ∧ symmDiffFold Finset.univ (fun x => canonicalTransferUnion ends m k zero (a x).1.1) = symmDiffFold Finset.univ (fun x => canonicalTransferUnion ends m k zero (b x).1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_canonicalTransferFoldCycle_obstruction ends m j k l zero hloop hjk hkl hk0 p hfail


-- created on 2026-10-23
