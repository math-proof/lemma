import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part8
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[canonicalMaskTransferAdjacent_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskTransferAdjacent_symm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Symmetric (CanonicalMaskTransferAdjacent ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferAdjacent_symm ends m j k l zero p

/--
[canonicalMaskTransferOrbit_refl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskTransferOrbit_refl_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalMaskTransferOrbit ends m j k l zero p c c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferOrbit_refl ends m j k l zero p c

/--
[canonicalMaskTransferOrbit_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskTransferOrbit_symm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Symmetric (CanonicalMaskTransferOrbit ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferOrbit_symm ends m j k l zero p

/--
[canonicalMaskTransferOrbit_trans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskTransferOrbit_trans_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Transitive (CanonicalMaskTransferOrbit ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferOrbit_trans ends m j k l zero p

/--
[canonicalMaskOrbitScore_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitScore_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Function.Injective (canonicalMaskOrbitScore ends m k zero p (j := j) (l := l)) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitScore_injective ends m j k l zero p

/--
[mem_canonicalMaskTransferOrbitFinset_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma mem_canonicalMaskTransferOrbitFinset_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c ↔ CanonicalMaskTransferOrbit ends m j k l zero p c d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalMaskTransferOrbitFinset_iff ends m j k l zero p c d

/--
[canonicalMaskTransferOrbitFinset_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskTransferOrbitFinset_nonempty_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  (canonicalMaskTransferOrbitFinset ends m j k l zero p c).Nonempty := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskTransferOrbitFinset_nonempty ends m j k l zero p c

/--
[canonicalMaskOrbitMinimumReference_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_spec_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  canonicalMaskOrbitMinimumReference ends m j k l zero p c ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c ∧ ∀ d ∈ canonicalMaskTransferOrbitFinset ends m j k l zero p c, canonicalMaskOrbitScore ends m k zero p (canonicalMaskOrbitMinimumReference ends m j k l zero p c) ≤ canonicalMaskOrbitScore ends m k zero p d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_spec ends m j k l zero p c

/--
[canonicalMaskOrbitMinimumReference_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_mem_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  CanonicalMaskTransferOrbit ends m j k l zero p c (canonicalMaskOrbitMinimumReference ends m j k l zero p c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_mem ends m j k l zero p c

/--
[canonicalMaskOrbitMinimumReference_score_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_score_le_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalMaskOrbitScore ends m k zero p (canonicalMaskOrbitMinimumReference ends m j k l zero p c) ≤ canonicalMaskOrbitScore ends m k zero p d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_score_le ends m j k l zero p c d hcd

/--
[canonicalMaskOrbitMinimumReference_size_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_size_le_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalTransferSize ends m k zero (canonicalMaskOrbitMinimumReference ends m j k l zero p c).1.1 ≤ canonicalTransferSize ends m k zero d.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_size_le ends m j k l zero p c d hcd

/--
[canonicalMaskOrbitMinimumReference_eq_of_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_eq_of_orbit_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalMaskOrbitMinimumReference ends m j k l zero p c = canonicalMaskOrbitMinimumReference ends m j k l zero p d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_eq_of_orbit ends m j k l zero p c d hcd

/--
[canonicalMaskOrbitMinimumReference_selector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_selector_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  IsCanonicalMaskOrbitSelector ends m j k l zero p (canonicalMaskOrbitMinimumReference ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_selector ends m j k l zero p

/--
[canonicalTransfers_valid_on_sameMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalTransfers_valid_on_sameMask_eq
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
  let X := canonicalMiddleTransfer ends m r.1.1 k zero let Y := canonicalOuterTransfer ends m r.1.1 k zero X ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 ∧ Y ⊆ colorClass m c.1.1 0 ∪ colorClass m c.1.1 3 ∧ sources ends X = {k, l} ∧ sources ends Y = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransfers_valid_on_sameMask hloop hjk hkl r c

/--
[leftMaskFiber_card_le_right_of_canonicalOrbitSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma leftMaskFiber_card_le_right_of_canonicalOrbitSelector_eq
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
  (rho : leftMaskFiber ends m j k l zero p -> leftMaskFiber ends m j k l zero p)
  (hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho)
  (hdisconnect : ∀ c, RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m (rho c).1.1 k zero) (canonicalOuterTransfer ends m (rho c).1.1 k zero) c.1.1) k zero) :
-- imply
  Fintype.card (leftMaskFiber ends m j k l zero p) ≤ Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskFiber_card_le_right_of_canonicalOrbitSelector ends m j k l zero hloop hjk hkl p rho hrho hdisconnect

/--
[canonicalMaskOrbitMinimumReference_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma canonicalMaskOrbitMinimumReference_disconnects_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {d : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hdescent : CanonicalMaskOrbitLocalDescent ends m j k l zero p) :
-- imply
  RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m (canonicalMaskOrbitMinimumReference ends m j k l zero p d).1.1 k zero) (canonicalOuterTransfer ends m (canonicalMaskOrbitMinimumReference ends m j k l zero p d).1.1 k zero) d.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskOrbitMinimumReference_disconnects ends m j k l zero p hdescent d

/--
[GrahamFiberMinor_of_canonicalMaskOrbitLocalDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalMaskOrbitLocalDescent_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hdescent : ∀ p : Finset I × Finset I, CanonicalMaskOrbitLocalDescent ends m j k l zero p) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalMaskOrbitLocalDescent ends m j k l zero hloop hjk hkl hdescent


-- created on 2026-10-23
