import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferGF2.Part3
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[eq_of_rowClass_zero_of_fourColorMaskProfile_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma eq_of_rowClass_zero_of_fourColorMaskProfile_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (c d : ↑m -> Fin 4)
  (hprofile : fourColorMaskProfile m c = fourColorMaskProfile m d)
  (hrow : rowClass m c 0 = rowClass m d 0) :
-- imply
  c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.eq_of_rowClass_zero_of_fourColorMaskProfile_eq m c d hprofile hrow

/--
[balancedSwap_comp_eq_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma balancedSwap_comp_eq_symmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {m X₁ Y₁ X₂ Y₂ : Finset I}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  balancedSwap m X₂ Y₂ (balancedSwap m X₁ Y₁ c) = balancedSwap m (X₁ ∆ X₂) (Y₁ ∆ Y₂) c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedSwap_comp_eq_symmDiff m X₁ Y₁ X₂ Y₂ c

/--
[canonicalTransferUnion_subset_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma canonicalTransferUnion_subset_m_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  canonicalTransferUnion ends m k zero r.1.1 ⊆ m := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferUnion_subset_m hloop hjk hkl r

/--
[canonicalTransferWorks_iff_translatedRowDisconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma canonicalTransferWorks_iff_translatedRowDisconnects_eq
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
  CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ↔ RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferWorks_iff_translatedRowDisconnects hloop hjk hkl r c

/--
[canonicalBalancedSwaps_eq_iff_rowSymmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma canonicalBalancedSwaps_eq_iff_rowSymmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  balancedSwap m (canonicalMiddleTransfer ends m a.1.1 k zero) (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 = balancedSwap m (canonicalMiddleTransfer ends m b.1.1 k zero) (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1 ↔ rowClass m c.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 = rowClass m d.1.1 0 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalBalancedSwaps_eq_iff_rowSymmDiff hloop hjk hkl a b c d

/--
[rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {k zero : W}
-- given
  (a b c d : ↑m -> Fin 4)
  (h : canonicalTranslatedRow ends m k zero a c = canonicalTranslatedRow ends m k zero b d) :
-- imply
  rowClass m c 0 ∆ rowClass m d 0 = canonicalTransferUnion ends m k zero a ∆ canonicalTransferUnion ends m k zero b := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq a b c d h

/--
[card_rowSymmDiff_eq_card_transferSymmDiff_of_translatedRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma card_rowSymmDiff_eq_card_transferSymmDiff_of_translatedRow_eq_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {k zero : W}
-- given
  (a b c d : ↑m -> Fin 4)
  (h : canonicalTranslatedRow ends m k zero a c = canonicalTranslatedRow ends m k zero b d) :
-- imply
  #(rowClass m c 0 ∆ rowClass m d 0) = #(canonicalTransferUnion ends m k zero a ∆ canonicalTransferUnion ends m k zero b) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_rowSymmDiff_eq_card_transferSymmDiff_of_translatedRow_eq a b c d h

/--
[canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  CanonicalMaskTransferAdjacent ends m j k l zero p c d ↔ ∃ a b : leftMaskFiber ends m j k l zero p, CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧ rowClass m c.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 = rowClass m d.1.1 0 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff hloop hjk hkl c d

/--
[canonicalMaskTransferAdjacent_iff_exists_translatedRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma canonicalMaskTransferAdjacent_iff_exists_translatedRow_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  CanonicalMaskTransferAdjacent ends m j k l zero p c d ↔ ∃ a b : leftMaskFiber ends m j k l zero p, RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero a.1.1 c.1.1) k zero ∧ canonicalTranslatedRow ends m k zero a.1.1 c.1.1 = canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferAdjacent_iff_exists_translatedRow hloop hjk hkl c d

/--
[mem_canonicalMaskOrbitCoverage_iff_translatedRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferGF2.lean)
-/
@[path]
private lemma mem_canonicalMaskOrbitCoverage_iff_translatedRow_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r d : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ↔ CanonicalMaskTransferOrbit ends m j k l zero p r d ∧ RowSupportDisconnects ends m (canonicalTranslatedRow ends m k zero r.1.1 d.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskOrbitCoverage_iff_translatedRow hloop hjk hkl r d


-- created on 2026-10-23
