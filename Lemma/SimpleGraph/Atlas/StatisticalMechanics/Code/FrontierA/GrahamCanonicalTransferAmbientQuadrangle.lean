import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[leftMaskFiberToSourceMaskFiber_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma leftMaskFiberToSourceMaskFiber_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  Function.Injective (leftMaskFiberToSourceMaskFiber ends m j k l zero p) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskFiberToSourceMaskFiber_injective ends m j k l zero p

/--
[leftSourcePattern_of_sourceless_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma leftSourcePattern_of_sourceless_balancedSwap_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m X Y : Finset I}
  {A B : Finset W}
  {c : ↑m -> Fin 4}
-- given
  (hleft : LeftSourcePattern ends m A B c)
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
  (hsrcX : sources ends X = ∅)
  (hsrcY : sources ends Y = ∅) :
-- imply
  LeftSourcePattern ends m A B (balancedSwap m X Y c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftSourcePattern_of_sourceless_balancedSwap hleft hX hY hsrcX hsrcY

/--
[canonicalQuadrangleCompletionSourceEquiv_commute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletionSourceEquiv_commute_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b r s : leftMaskFiber ends m j k l zero p}
  {x : leftSourceMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  canonicalQuadrangleCompletionSourceEquiv ends m j k l zero hloop hjk hkl p a b (canonicalQuadrangleCompletionSourceEquiv ends m j k l zero hloop hjk hkl p r s x) = canonicalQuadrangleCompletionSourceEquiv ends m j k l zero hloop hjk hkl p r s (canonicalQuadrangleCompletionSourceEquiv ends m j k l zero hloop hjk hkl p a b x) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletionSourceEquiv_commute ends m j k l zero hloop hjk hkl p a b r s x

/--
[mem_canonicalCoverageExclusiveGoodQuadrangles_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma mem_canonicalCoverageExclusiveGoodQuadrangles_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  c ∈ canonicalCoverageExclusiveGoodQuadrangles ends m j k l zero p a b ↔ c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧ c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ∧ RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalCoverageExclusiveGoodQuadrangles_iff ends m j k l zero p a b c

/--
[canonicalCoverageExclusiveGoodSwap_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma canonicalCoverageExclusiveGoodSwap_injective_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
-- imply
  Function.Injective (canonicalCoverageExclusiveGoodSwap ends m j k l zero hloop hjk hkl p a b hab) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoverageExclusiveGoodSwap_injective ends m j k l zero hloop hjk hkl p a b hab

/--
[card_canonicalCoverageExclusiveGoodQuadrangles_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma card_canonicalCoverageExclusiveGoodQuadrangles_comm_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
-- imply
  #(canonicalCoverageExclusiveGoodQuadrangles ends m j k l zero p a b) = #(canonicalCoverageExclusiveGoodQuadrangles ends m j k l zero p b a) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_canonicalCoverageExclusiveGoodQuadrangles_comm ends m j k l zero hloop hjk hkl p a b hab

/--
[mem_canonicalCoverageExclusiveBadQuadrangles_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma mem_canonicalCoverageExclusiveBadQuadrangles_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  c ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b ↔ c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧ c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ∧ ¬ RowsDisconnect ends m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalCoverageExclusiveBadQuadrangles_iff ends m j k l zero p a b c

/--
[card_good_add_bad_eq_card_coverage_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma card_good_add_bad_eq_card_coverage_sdiff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W) :
-- imply
  #(canonicalCoverageExclusiveGoodQuadrangles ends m j k l zero p a b) + #(canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b) = #(canonicalCoverageExclusive ends m j k l zero p a b) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.card_good_add_bad_eq_card_coverage_sdiff ends m j k l zero p a b

/--
[coverage_card_add_bad_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma coverage_card_add_bad_swap_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
-- imply
  #(canonicalMaskOrbitCoverage ends m j k l zero p a) + #(canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p b a) = #(canonicalMaskOrbitCoverage ends m j k l zero p b) + #(canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.coverage_card_add_bad_swap ends m j k l zero hloop hjk hkl p a b hab

/--
[coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferAmbientQuadrangle.lean)
-/
@[path]
private lemma coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
  (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b)
  (hopposite : canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p b a = ∅) :
-- imply
  #(canonicalMaskOrbitCoverage ends m j k l zero p b) < #(canonicalMaskOrbitCoverage ends m j k l zero p a) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty ends m j k l zero hloop hjk hkl p a b c hab hc hopposite


-- created on 2026-10-23
