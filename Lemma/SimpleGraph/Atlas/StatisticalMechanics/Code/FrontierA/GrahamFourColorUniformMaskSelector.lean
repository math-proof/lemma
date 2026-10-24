import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[middleMask_disjoint_outerMask](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma middleMask_disjoint_outerMask_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  Disjoint (middleMask m c) (outerMask m c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleMask_disjoint_outerMask m c

/--
[canonicalTransferSize_eq_card_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma canonicalTransferSize_eq_card_union_eq
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι -> Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  canonicalTransferSize ends m k zero c = #(canonicalTransferUnion ends m k zero c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferSize_eq_card_union hloop hjk hkl hc

/--
[leftMaskReference_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma leftMaskReference_spec_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
  {p : Finset ι × Finset ι}
-- given
  (ends : ι -> Sym2 W)
  (h : ∃ c : ↑m -> Fin 4, LeftPattern ends m {j, k} {k, l} k zero c ∧ fourColorMaskProfile m c = p) :
-- imply
  LeftPattern ends m {j, k} {k, l} k zero (leftMaskReference ends m j k l zero p) ∧ fourColorMaskProfile m (leftMaskReference ends m j k l zero p) = p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskReference_spec ends m j k l zero p h

/--
[leftMaskReference_minimal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma leftMaskReference_minimal_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
  {p : Finset ι × Finset ι}
-- given
  (ends : ι -> Sym2 W)
  (h : ∃ c : ↑m -> Fin 4, LeftPattern ends m {j, k} {k, l} k zero c ∧ fourColorMaskProfile m c = p)
  (d : ↑m -> Fin 4)
  (hd : LeftPattern ends m {j, k} {k, l} k zero d)
  (hdp : fourColorMaskProfile m d = p) :
-- imply
  canonicalTransferSize ends m k zero (leftMaskReference ends m j k l zero p) <= canonicalTransferSize ends m k zero d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftMaskReference_minimal ends m j k l zero p h d hd hdp

/--
[fourColorMaskProfile_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma fourColorMaskProfile_balancedSwap_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  fourColorMaskProfile m (balancedSwap m X Y c) = fourColorMaskProfile m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.fourColorMaskProfile_balancedSwap m X Y c

/--
[uniformMaskCanonicalSelector_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma uniformMaskCanonicalSelector_balancedSwap_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  uniformMaskCanonicalSelector ends m j k l zero (balancedSwap m X Y c) = uniformMaskCanonicalSelector ends m j k l zero c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.uniformMaskCanonicalSelector_balancedSwap ends m X Y j k l zero c

/--
[uniformMaskCanonicalSelector_valid_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma uniformMaskCanonicalSelector_valid_sources_eq
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι -> Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  let s := uniformMaskCanonicalSelector ends m j k l zero c s.1 ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧ s.2 ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧ sources ends s.1 = {k, l} ∧ sources ends s.2 = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.uniformMaskCanonicalSelector_valid_sources hloop hjk hkl hc

/--
[GrahamFiberMinor_of_uniformMaskCanonicalTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_uniformMaskCanonicalTransfer_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hdisconnect : ∀ c : ↑m -> Fin 4, LeftPattern ends m {j, k} {k, l} k zero c -> let s := uniformMaskCanonicalSelector ends m j k l zero c RowsDisconnect ends m (balancedSwap m s.1 s.2 c) k zero) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_uniformMaskCanonicalTransfer ends m j k l zero hloop hjk hkl hdisconnect

/--
[GrahamFiberMinor_of_canonicalTransferDescent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalTransferDescent_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hdescent : ∀ c d : ↑m -> Fin 4, LeftPattern ends m {j, k} {k, l} k zero c -> LeftPattern ends m {j, k} {k, l} k zero d -> fourColorMaskProfile m c = fourColorMaskProfile m d -> ¬ RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) d) k zero -> canonicalTransferSize ends m k zero d < canonicalTransferSize ends m k zero c) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalTransferDescent ends m j k l zero hloop hjk hkl hdescent

/--
[GrahamFiberMinor_of_canonicalTransferStrictSubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_canonicalTransferStrictSubset_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {j k l zero : W}
-- given
  (ends : ι -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hproper : ∀ c d : ↑m -> Fin 4, LeftPattern ends m {j, k} {k, l} k zero c -> LeftPattern ends m {j, k} {k, l} k zero d -> fourColorMaskProfile m c = fourColorMaskProfile m d -> ¬ RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) d) k zero -> canonicalTransferUnion ends m k zero d ⊂ canonicalTransferUnion ends m k zero c) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_canonicalTransferStrictSubset ends m j k l zero hloop hjk hkl hproper


-- created on 2026-10-23
