import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching.Part2
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[nonempty_maskFiberEmbeddings_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma nonempty_maskFiberEmbeddings_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Nonempty (MaskFiberEmbeddings ends m j k l zero) ↔ forall p : Finset I × Finset I, Fintype.card (leftMaskFiber ends m j k l zero p) <= Fintype.card (rightMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.nonempty_maskFiberEmbeddings_iff ends m j k l zero

/--
[GrahamFiberMinor_of_maskFiberEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_maskFiberEmbeddings_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {f : MaskFiberEmbeddings ends m j k l zero}
-- given
  (ends : I -> Sym2 W) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_maskFiberEmbeddings ends m j k l zero f

/--
[maskFiberEmbedding_differenceTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma maskFiberEmbedding_differenceTransfer_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {f : MaskFiberEmbeddings ends m j k l zero}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  let d := (f p c).1.1 let X := balancedMiddleDifference m c.1.1 d let Y := balancedOuterDifference m c.1.1 d X ⊆ middleMask m c.1.1 ∧ Y ⊆ outerMask m c.1.1 ∧ sources ends X = {k, l} ∧ sources ends Y = ∅ ∧ BalancedRepairAdmissible ends m X k zero c.1.1 Y ∧ balancedSwap m X Y c.1.1 = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.maskFiberEmbedding_differenceTransfer ends m j k l zero f c

/--
[eq_of_middle_outer_colorClass_one_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma eq_of_middle_outer_colorClass_one_three_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
-- given
  (c d : ↑m -> Fin 4)
  (hmid : middleMask m c = middleMask m d)
  (hout : outerMask m c = outerMask m d)
  (hone : colorClass m c 1 = colorClass m d 1)
  (hthree : colorClass m c 3 = colorClass m d 3) :
-- imply
  c = d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.eq_of_middle_outer_colorClass_one_three m c d hmid hout hone hthree

/--
[subsingleton_leftMaskFiber_of_cycleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma subsingleton_leftMaskFiber_of_cycleSectors_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hmiddle : Subsingleton (boundarySector ends p.1 ∅))
  (houter : Subsingleton (boundarySector ends p.2 ∅)) :
-- imply
  Subsingleton (leftMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.subsingleton_leftMaskFiber_of_cycleSectors ends m j k l zero p hmiddle houter

/--
[GrahamFiberMinor_of_subsingleton_leftMaskFibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_subsingleton_leftMaskFibers_eq
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
  (hsub : ∀ p : Finset I × Finset I, Subsingleton (leftMaskFiber ends m j k l zero p)) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_subsingleton_leftMaskFibers ends m j k l zero hloop hjk hkl hk0 hsub

/--
[GrahamFiberMinor_of_subsingleton_cycleSectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_subsingleton_cycleSectors_eq
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
  (hcycle : ∀ p : Finset I × Finset I, Subsingleton (boundarySector ends p.1 ∅) ∧ Subsingleton (boundarySector ends p.2 ∅)) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_subsingleton_cycleSectors ends m j k l zero hloop hjk hkl hk0 hcycle


-- created on 2026-10-23
