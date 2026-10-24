import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[boundarySector_card_eq_cycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma boundarySector_card_eq_cycle_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {S : Finset ι}
  {b : Finset W}
  {X : boundarySector ends S b} :
-- imply
  Fintype.card (boundarySector ends S b) = Fintype.card (boundarySector ends S ∅) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.boundarySector_card_eq_cycle ends S b X

/--
[colorClass_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_subset_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4}
  {a : Fin 4} :
-- imply
  colorClass m c a ⊆ m := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_subset m c a

/--
[colorClass_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_disjoint_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4}
  {a b : Fin 4}
-- given
  (hab : a ≠ b) :
-- imply
  Disjoint (colorClass m c a) (colorClass m c b) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_disjoint m c hab

/--
[connK_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma connK_mono_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K L : Finset ι}
  {u v : W}
-- given
  (hKL : K ⊆ L) :
-- imply
  Sharpness.RandomCurrent.connK ends K u v → Sharpness.RandomCurrent.connK ends L u v := by
-- proof
  apply StatMech.GrahamGHS.FourColor.connK_mono hKL

/--
[mem_edgeComponent_of_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma mem_edgeComponent_of_endpoint_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u : W}
  {i : ι}
-- given
  (hi : i ∈ K)
  (hu : u ∈ ends i) :
-- imply
  i ∈ edgeComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_edgeComponent_of_endpoint hi hu

/--
[mem_edgeComponent_of_reachable_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma mem_edgeComponent_of_reachable_endpoint_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u x : W}
  {i : ι}
-- given
  (hux : Sharpness.RandomCurrent.connK ends K u x)
  (hi : i ∈ K)
  (hx : x ∈ ends i) :
-- imply
  i ∈ edgeComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_edgeComponent_of_reachable_endpoint hux hi hx

/--
[degK_inter_edgeComponent_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma degK_inter_edgeComponent_of_conn_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {T K : Finset ι}
  {u x : W}
-- given
  (hTK : T ⊆ K)
  (hux : Sharpness.RandomCurrent.connK ends K u x) :
-- imply
  Sharpness.RandomCurrent.degK ends (T ∩ edgeComponent ends K u) x = Sharpness.RandomCurrent.degK ends T x := by
-- proof
  apply StatMech.GrahamGHS.FourColor.degK_inter_edgeComponent_of_conn hTK hux

/--
[degK_inter_edgeComponent_of_not_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma degK_inter_edgeComponent_of_not_conn_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {T K : Finset ι}
  {u x : W}
-- given
  (hux : ¬ Sharpness.RandomCurrent.connK ends K u x) :
-- imply
  Sharpness.RandomCurrent.degK ends (T ∩ edgeComponent ends K u) x = 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.degK_inter_edgeComponent_of_not_conn hux

/--
[sources_inter_edgeComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma sources_inter_edgeComponent_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {T K : Finset ι}
  {u : W}
-- given
  (hTK : T ⊆ K) :
-- imply
  Sharpness.RandomCurrent.sources ends (T ∩ edgeComponent ends K u) = Sharpness.RandomCurrent.sources ends T ∩ Sharpness.RandomCurrent.compOf ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_inter_edgeComponent hTK u

/--
[sources_union_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma sources_union_of_disjoint_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {S T : Finset ι}
-- given
  (hST : Disjoint S T) :
-- imply
  Sharpness.RandomCurrent.sources ends (S ∪ T) = Sharpness.RandomCurrent.sources ends S ∆ Sharpness.RandomCurrent.sources ends T := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_union_of_disjoint hST

/--
[sources_sdiff_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma sources_sdiff_of_subset_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {S T : Finset ι}
-- given
  (hTS : T ⊆ S) :
-- imply
  Sharpness.RandomCurrent.sources ends (S \ T) = Sharpness.RandomCurrent.sources ends S ∆ Sharpness.RandomCurrent.sources ends T := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_sdiff_of_subset hTS

/--
[sources_edgeComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma sources_edgeComponent_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u : W} :
-- imply
  Sharpness.RandomCurrent.sources ends (edgeComponent ends K u) = Sharpness.RandomCurrent.sources ends K ∩ Sharpness.RandomCurrent.compOf ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_edgeComponent K u

/--
[not_connK_of_no_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma not_connK_of_no_incident_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K : Finset ι}
  {u v : W}
-- given
  (huv : u ≠ v)
  (hinc : ∀ i ∈ K, u ∉ ends i) :
-- imply
  ¬ Sharpness.RandomCurrent.connK ends K u v := by
-- proof
  apply StatMech.GrahamGHS.FourColor.not_connK_of_no_incident huv hinc

/--
[componentExchange_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma componentExchange_disconnects_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K L : Finset ι}
  {k zero : W}
-- given
  (hk0 : k ≠ zero)
  (hK : ¬ Sharpness.RandomCurrent.connK ends K k zero)
  (hL : ¬ Sharpness.RandomCurrent.connK ends L k zero) :
-- imply
  ¬ Sharpness.RandomCurrent.connK ends (exchangeFirstRow ends K L k zero) k zero ∧ ¬ Sharpness.RandomCurrent.connK ends (exchangeSecondRow ends K L k zero) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.componentExchange_disconnects hk0 hK hL

/--
[componentExchange_boundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma componentExchange_boundaries_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {K L : Finset ι}
  {j k l zero : W}
-- given
  (hloopK : ∀ i ∈ K, ¬ (ends i).IsDiag)
  (hloopL : ∀ i ∈ L, ¬ (ends i).IsDiag)
  (hKL : Disjoint K L)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hsrcK : Sharpness.RandomCurrent.sources ends K = {j, k})
  (hsrcL : Sharpness.RandomCurrent.sources ends L = {k, l})
  (hdiscK : ¬ Sharpness.RandomCurrent.connK ends K k zero)
  (hdiscL : ¬ Sharpness.RandomCurrent.connK ends L k zero) :
-- imply
  Sharpness.RandomCurrent.sources ends (exchangeFirstRow ends K L k zero) = {j, k} ∆ {k, l} ∧ Sharpness.RandomCurrent.sources ends (exchangeSecondRow ends K L k zero) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.componentExchange_boundaries hloopK hloopL hKL hjk hkl hsrcK hsrcL hdiscK hdiscL

/--
[middleSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma middleSwap_involutive_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  middleSwap m (middleSwap m c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleSwap_involutive m c

/--
[colorClass_middleSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_middleSwap_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4}
  {a : Fin 4} :
-- imply
  colorClass m (middleSwap m c) a = colorClass m c (Equiv.swap (1 : Fin 4) 2 a) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_middleSwap m c a

/--
[middleSwapOn_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma middleSwapOn_involutive_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  middleSwapOn m X (middleSwapOn m X c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.middleSwapOn_involutive m X c

/--
[colorClass_middleSwapOn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_middleSwapOn_zero_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  colorClass m (middleSwapOn m X c) 0 = colorClass m c 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_middleSwapOn_zero m X c

/--
[colorClass_middleSwapOn_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_middleSwapOn_three_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  colorClass m (middleSwapOn m X c) 3 = colorClass m c 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_middleSwapOn_three m X c

/--
[colorClass_middleSwapOn_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_middleSwapOn_one_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {c : ↑m → Fin 4}
-- given
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2) :
-- imply
  colorClass m (middleSwapOn m X c) 1 = colorClass m c 1 ∆ X := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_middleSwapOn_one m X c hX

/--
[colorClass_middleSwapOn_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_middleSwapOn_two_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X : Finset ι}
  {c : ↑m → Fin 4}
-- given
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2) :
-- imply
  colorClass m (middleSwapOn m X c) 2 = colorClass m c 2 ∆ X := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_middleSwapOn_two m X c hX

/--
[outerSwapOn_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma outerSwapOn_involutive_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m Y : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  outerSwapOn m Y (outerSwapOn m Y c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.outerSwapOn_involutive m Y c

/--
[colorClass_outerSwapOn_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_outerSwapOn_one_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m Y : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  colorClass m (outerSwapOn m Y c) 1 = colorClass m c 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_outerSwapOn_one m Y c

/--
[colorClass_outerSwapOn_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_outerSwapOn_two_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m Y : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  colorClass m (outerSwapOn m Y c) 2 = colorClass m c 2 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_outerSwapOn_two m Y c

/--
[colorClass_outerSwapOn_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_outerSwapOn_zero_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m Y : Finset ι}
  {c : ↑m → Fin 4}
-- given
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
-- imply
  colorClass m (outerSwapOn m Y c) 0 = colorClass m c 0 ∆ Y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_outerSwapOn_zero m Y c hY

/--
[colorClass_outerSwapOn_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClass_outerSwapOn_three_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m Y : Finset ι}
  {c : ↑m → Fin 4}
-- given
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
-- imply
  colorClass m (outerSwapOn m Y c) 3 = colorClass m c 3 ∆ Y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClass_outerSwapOn_three m Y c hY

/--
[balancedSwap_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma balancedSwap_involutive_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  balancedSwap m X Y (balancedSwap m X Y c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.balancedSwap_involutive m X Y c

/--
[rowClass_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowClass_zero_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  rowClass m c 0 = colorClass m c 0 ∪ colorClass m c 1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_zero m c

/--
[rowClass_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowClass_one_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  rowClass m c 1 = colorClass m c 2 ∪ colorClass m c 3 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_one m c

/--
[rowClass_balancedSwap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowClass_balancedSwap_zero_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
  {c : ↑m → Fin 4}
-- given
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
-- imply
  rowClass m (balancedSwap m X Y c) 0 = rowClass m c 0 ∆ (X ∪ Y) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_balancedSwap_zero hX hY

/--
[rowClass_one_eq_sdiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowClass_one_eq_sdiff_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m : Finset ι}
  {c : ↑m → Fin 4} :
-- imply
  rowClass m c 1 = m \ rowClass m c 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_one_eq_sdiff m c

/--
[colorClasses_coloringOfRowData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma colorClasses_coloringOfRowData_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m K P Q : Finset ι}
-- given
  (hKm : K ⊆ m)
  (hPK : P ⊆ K)
  (hQL : Q ⊆ m \ K) :
-- imply
  colorClass m (coloringOfRowData m K P Q) 0 = P ∧ colorClass m (coloringOfRowData m K P Q) 1 = K \ P ∧ colorClass m (coloringOfRowData m K P Q) 2 = Q ∧ colorClass m (coloringOfRowData m K P Q) 3 = (m \ K) \ Q := by
-- proof
  apply StatMech.GrahamGHS.FourColor.colorClasses_coloringOfRowData hKm hPK hQL

/--
[rowClasses_coloringOfRowData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowClasses_coloringOfRowData_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m K P Q : Finset ι}
-- given
  (hKm : K ⊆ m)
  (hPK : P ⊆ K)
  (hQL : Q ⊆ m \ K) :
-- imply
  rowClass m (coloringOfRowData m K P Q) 0 = K ∧ rowClass m (coloringOfRowData m K P Q) 1 = m \ K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClasses_coloringOfRowData hKm hPK hQL

/--
[rowClass_balancedSwap_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowClass_balancedSwap_one_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {m X Y : Finset ι}
  {c : ↑m → Fin 4}
-- given
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3) :
-- imply
  rowClass m (balancedSwap m X Y c) 1 = rowClass m c 1 ∆ (X ∪ Y) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_balancedSwap_one hX hY

/--
[mem_rowComponent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma mem_rowComponent_iff_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {c : ↑m → Fin 4}
  {r : Fin 2}
  {u x : W} :
-- imply
  x ∈ rowComponent ends m c r u ↔ Sharpness.RandomCurrent.connK ends (rowClass m c r) u x := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_rowComponent_iff ends m c r u x

/--
[rowsDisconnect_iff_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowsDisconnect_iff_component_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {c : ↑m → Fin 4}
  {u v : W} :
-- imply
  RowsDisconnect ends m c u v ↔ v ∉ rowComponent ends m c 0 u ∧ v ∉ rowComponent ends m c 1 u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowsDisconnect_iff_component ends m c u v

/--
[rowComponent_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowComponent_noCrossing_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {c : ↑m → Fin 4}
  {r : Fin 2}
  {u : W} :
-- imply
  Sharpness.RandomCurrent.NoCrossingK ends (rowClass m c r) (Sharpness.RandomCurrent.notConnCompK ends (rowClass m c r) u) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowComponent_noCrossing ends m c r u

/--
[rightPattern_of_middleTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rightPattern_of_middleTransfer_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m X : Finset ι}
  {A B : Finset W}
  {u v : W}
  {c : ↑m → Fin 4}
-- given
  (hleft : LeftPattern ends m A B u v c)
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hsrc : Sharpness.RandomCurrent.sources ends X = B)
  (hdisc : RowsDisconnect ends m (middleSwapOn m X c) u v) :
-- imply
  RightPattern ends m A B u v (middleSwapOn m X c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightPattern_of_middleTransfer hleft hX hsrc hdisc

/--
[rightPattern_of_balancedTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rightPattern_of_balancedTransfer_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m X Y : Finset ι}
  {A B : Finset W}
  {u v : W}
  {c : ↑m → Fin 4}
-- given
  (hleft : LeftPattern ends m A B u v c)
  (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
  (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
  (hsrcX : Sharpness.RandomCurrent.sources ends X = B)
  (hsrcY : Sharpness.RandomCurrent.sources ends Y = ∅)
  (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
-- imply
  RightPattern ends m A B u v (balancedSwap m X Y c) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightPattern_of_balancedTransfer hleft hX hY hsrcX hsrcY hdisc

/--
[leftPattern_sharedSource_connections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma leftPattern_sharedSource_connections_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m → Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  Sharpness.RandomCurrent.connK ends (colorClass m c 0) j k ∧ Sharpness.RandomCurrent.connK ends (colorClass m c 2) k l := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_sharedSource_connections hloop hjk hkl h

/--
[leftPattern_sharedSource_avoids_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma leftPattern_sharedSource_avoids_zero_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m → Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 0) j zero ∧ ¬ Sharpness.RandomCurrent.connK ends (rowClass m c 1) l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_sharedSource_avoids_zero hloop hjk hkl h

/--
[canonicalTransfers_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma canonicalTransfers_valid_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m → Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  canonicalMiddleTransfer ends m c k zero ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧ canonicalOuterTransfer ends m c k zero ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧ Sharpness.RandomCurrent.sources ends (canonicalMiddleTransfer ends m c k zero) = {k, l} ∧ Sharpness.RandomCurrent.sources ends (canonicalOuterTransfer ends m c k zero) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransfers_valid hloop hjk hkl h

/--
[canonicalTransfers_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma canonicalTransfers_union_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {k zero : W}
  {c : ↑m → Fin 4} :
-- imply
  canonicalMiddleTransfer ends m c k zero ∪ canonicalOuterTransfer ends m c k zero = edgeComponent ends (rowClass m c 0) zero ∪ edgeComponent ends (rowClass m c 1) k := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransfers_union

/--
[symmDiff_componentExchange_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma symmDiff_componentExchange_first_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {K L A B : Finset ι}
-- given
  (hA : A ⊆ K)
  (hB : B ⊆ L)
  (hKL : Disjoint K L) :
-- imply
  K ∆ (A ∪ B) = (K \ A) ∪ B := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiff_componentExchange_first hA hB hKL

/--
[symmDiff_componentExchange_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma symmDiff_componentExchange_second_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {K L A B : Finset ι}
-- given
  (hA : A ⊆ K)
  (hB : B ⊆ L)
  (hKL : Disjoint K L) :
-- imply
  L ∆ (A ∪ B) = (L \ B) ∪ A := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiff_componentExchange_second hA hB hKL

/--
[canonicalBalancedSwap_rows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma canonicalBalancedSwap_rows_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m → Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) c) 0 = exchangeFirstRow ends (rowClass m c 0) (rowClass m c 1) k zero ∧ rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) c) 1 = exchangeSecondRow ends (rowClass m c 0) (rowClass m c 1) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalBalancedSwap_rows hloop hjk hkl h

/--
[canonicalBalancedSwap_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma canonicalBalancedSwap_disconnects_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : ↑m → Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (h : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  RowsDisconnect ends m (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) c) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalBalancedSwap_disconnects hloop hjk hkl hk0 h

/--
[leftPattern_componentExchange_disconnects](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma leftPattern_componentExchange_disconnects_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {k zero : W}
  {c : ↑m → Fin 4}
-- given
  (hk0 : k ≠ zero)
  (h : LeftPattern ends m A B k zero c) :
-- imply
  ¬ Sharpness.RandomCurrent.connK ends (exchangeFirstRow ends (rowClass m c 0) (rowClass m c 1) k zero) k zero ∧ ¬ Sharpness.RandomCurrent.connK ends (exchangeSecondRow ends (rowClass m c 0) (rowClass m c 1) k zero) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_componentExchange_disconnects hk0 h

/--
[leftPattern_rowBoundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma leftPattern_rowBoundaries_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
  {c : ↑m → Fin 4}
-- given
  (h : LeftPattern ends m A B u v c) :
-- imply
  Sharpness.RandomCurrent.sources ends (rowClass m c 0) = A ∧ Sharpness.RandomCurrent.sources ends (rowClass m c 1) = B := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftPattern_rowBoundaries h

/--
[rightPattern_rowBoundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rightPattern_rowBoundaries_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
  {c : ↑m → Fin 4}
-- given
  (h : RightPattern ends m A B u v c) :
-- imply
  Sharpness.RandomCurrent.sources ends (rowClass m c 0) = A ∆ B ∧ Sharpness.RandomCurrent.sources ends (rowClass m c 1) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightPattern_rowBoundaries h

/--
[rowDataToLeftFiber_leftInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowDataToLeftFiber_leftInverse_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : leftFiber ends m {j, k} {k, l} k zero} :
-- imply
  rowDataToLeftFiber ends m j k l zero (leftFiberToRowData ends m j k l zero c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataToLeftFiber_leftInverse ends m j k l zero c

/--
[rowDataToLeftFiber_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowDataToLeftFiber_injective_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  Function.Injective (rowDataToLeftFiber ends m j k l zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataToLeftFiber_injective ends m j k l zero

/--
[leftRowData_card_eq_weightedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma leftRowData_card_eq_weightedSum_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  Fintype.card (leftRowData ends m j k l zero) = ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftRowData_card_eq_weightedSum ends m j k l zero

/--
[leftFiber_card_eq_weightedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma leftFiber_card_eq_weightedSum_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  Fintype.card (leftFiber ends m {j, k} {k, l} k zero) = ∑ K ∈ leftRowSupports ends m j k l zero, rowSupportWeight ends m K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.leftFiber_card_eq_weightedSum ends m j k l zero

/--
[rowDataToRightFiber_leftInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowDataToRightFiber_leftInverse_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {c : rightFiber ends m {j, k} {k, l} k zero} :
-- imply
  rowDataToRightFiber ends m j k l zero (rightFiberToRowData ends m j k l zero c) = c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataToRightFiber_leftInverse ends m j k l zero c

/--
[rowDataToRightFiber_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rowDataToRightFiber_injective_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  Function.Injective (rowDataToRightFiber ends m j k l zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowDataToRightFiber_injective ends m j k l zero

/--
[rightRowData_card_eq_weightedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rightRowData_card_eq_weightedSum_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  Fintype.card (rightRowData ends m j k l zero) = ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightRowData_card_eq_weightedSum ends m j k l zero

/--
[rightFiber_card_eq_weightedSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma rightFiber_card_eq_weightedSum_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  Fintype.card (rightFiber ends m {j, k} {k, l} k zero) = ∑ K ∈ rightRowSupports ends m j k l zero, rowSupportWeight ends m K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rightFiber_card_eq_weightedSum ends m j k l zero

/--
[GrahamFiberMinor_of_weightedRowMinor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_weightedRowMinor_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
-- given
  (h : GrahamWeightedRowMinor ends m j k l zero) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_weightedRowMinor ends m j k l zero h

/--
[GrahamFiberMinor_iff_weightedRowMinor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma GrahamFiberMinor_iff_weightedRowMinor_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W} :
-- imply
  GrahamFiberMinor ends m j k l zero ↔ GrahamWeightedRowMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_iff_weightedRowMinor ends m j k l zero

/--
[componentExchange_maps_leftRowSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma componentExchange_maps_leftRowSupport_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m K : Finset ι}
  {j k l zero : W}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hKm : K ⊆ m)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hk0 : k ≠ zero)
  (hleft : LeftRowSupport ends m j k l zero K) :
-- imply
  let K' := exchangeFirstRow ends K (m \ K) k zero K' ⊆ m ∧ RightRowSupport ends m j k l zero K' := by
-- proof
  apply StatMech.GrahamGHS.FourColor.componentExchange_maps_leftRowSupport hloop hKm hjk hkl hk0 hleft

/--
[GrahamFiberMinor_of_balancedSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_balancedSelector_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
  {σ : (↑m → Fin 4) → Finset ι × Finset ι}
-- given
  (hvalid : ∀ c, LeftPattern ends m {j, k} {k, l} k zero c → let X := (σ c).1 let Y := (σ c).2 X ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧ Y ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧ Sharpness.RandomCurrent.sources ends X = {k, l} ∧ Sharpness.RandomCurrent.sources ends Y = ∅ ∧ RowsDisconnect ends m (balancedSwap m X Y c) k zero)
  (hequiv : ∀ c, σ (balancedSwap m (σ c).1 (σ c).2 c) = σ c) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_balancedSelector ends m j k l zero σ hvalid hequiv

/--
[FiberMinorCandidate_of_total_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma FiberMinorCandidate_of_total_disconnected_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {A B : Finset W}
  {u v : W}
-- given
  (hdisc : ¬ Sharpness.RandomCurrent.connK ends m u v) :
-- imply
  FiberMinorCandidate ends m A B u v := by
-- proof
  apply StatMech.GrahamGHS.FourColor.FiberMinorCandidate_of_total_disconnected ends m A B u v hdisc

/--
[GrahamFiberMinor_of_total_disconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean)
-/
@[path]
private lemma GrahamFiberMinor_of_total_disconnected_eq
  [Fintype W]
  [DecidableEq W]
  [Fintype ι]
  [DecidableEq ι]
  {ends : ι → Sym2 W}
  {m : Finset ι}
  {j k l zero : W}
-- given
  (hdisc : ¬ Sharpness.RandomCurrent.connK ends m k zero) :
-- imply
  GrahamFiberMinor ends m j k l zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.GrahamFiberMinor_of_total_disconnected ends m j k l zero hdisc


-- created on 2026-10-23
