import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
open Finset Classical StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[mem_colorClass_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma mem_colorClass_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {a : Fin 4}
  {i : ι}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  i ∈ colorClass m c a ↔ ∃ hi : i ∈ m, c ⟨i, hi⟩ = a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_colorClass_iff m c a i

/--
[middleMask_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma middleMask_balancedSwap_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  middleMask m (balancedSwap m X Y c) = middleMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleMask_balancedSwap m X Y c

/--
[outerMask_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma outerMask_balancedSwap_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
-- given
  (c : ↑m -> Fin 4) :
-- imply
  outerMask m (balancedSwap m X Y c) = outerMask m c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.outerMask_balancedSwap m X Y c

/--
[leftPattern_middleMask_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma leftPattern_middleMask_sources_eq
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι -> Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  sources ends (middleMask m c) = {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_middleMask_sources h

/--
[leftPattern_outerMask_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma leftPattern_outerMask_sources_eq
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι -> Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  sources ends (outerMask m c) = {j, k} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_outerMask_sources h

/--
[leftPattern_middleComponent_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma leftPattern_middleComponent_sources_eq
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
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  sources ends (edgeComponent ends (middleMask m c) k) = {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_middleComponent_sources hloop hjk hkl h

/--
[middleComponent_balancedSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean)
-/
@[path]
private lemma middleComponent_balancedSwap_eq
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
  {k : W}
-- given
  (ends : ι -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  edgeComponent ends (middleMask m (balancedSwap m X Y c)) k = edgeComponent ends (middleMask m c) k := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleComponent_balancedSwap ends m X Y c k


-- created on 2026-10-23
