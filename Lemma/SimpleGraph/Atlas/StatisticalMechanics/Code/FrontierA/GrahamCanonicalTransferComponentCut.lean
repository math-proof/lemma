import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
open Finset StatMech StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[edgeComponent_eq_grahamSuperpositionBondComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma edgeComponent_eq_grahamSuperpositionBondComponent_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W) :
-- imply
  edgeComponent ends K u = StatMech.FrontierA.grahamSuperpositionBondComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.edgeComponent_eq_grahamSuperpositionBondComponent ends K u

/--
[mem_sdiff_edgeComponent_iff_edgeInside_componentComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_sdiff_edgeComponent_iff_edgeInside_componentComplement_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u : W}
  {i : I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  i ∈ K \ edgeComponent ends K u ↔ i ∈ K ∧ edgeInsideK ends (StatMech.FrontierA.grahamComponentComplement ends K u) i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_sdiff_edgeComponent_iff_edgeInside_componentComplement ends K u

/--
[edgeComponentComplement_noCrossing_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma edgeComponentComplement_noCrossing_of_subset_eq
  [Fintype I]
  [DecidableEq I]
  {K L : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hLK : L ⊆ K) :
-- imply
  NoCrossingK ends L (StatMech.FrontierA.grahamComponentComplement ends K u) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.edgeComponentComplement_noCrossing_of_subset ends K L u hLK

/--
[connK_mem_of_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma connK_mem_of_noCrossing_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {K : Finset I}
  {S : Finset W}
  {u x : W}
-- given
  (hcross : NoCrossingK ends K S)
  (hu : u ∈ S)
  (hux : connK ends K u x) :
-- imply
  x ∈ S := by
-- proof
  apply StatMech.GrahamGHS.FourColor.connK_mem_of_noCrossing hcross hu hux

/--
[connK_not_mem_of_noCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma connK_not_mem_of_noCrossing_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {K : Finset I}
  {S : Finset W}
  {u x : W}
-- given
  (hcross : NoCrossingK ends K S)
  (hu : u ∉ S)
  (hux : connK ends K u x) :
-- imply
  x ∉ S := by
-- proof
  apply StatMech.GrahamGHS.FourColor.connK_not_mem_of_noCrossing hcross hu hux

/--
[exists_crossing_edge_mem_sdiff_of_connK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_crossing_edge_mem_sdiff_of_connK_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {K L : Finset I}
  {S : Finset W}
  {u x : W}
-- given
  (hcross : NoCrossingK ends K S)
  (hu : u ∉ S)
  (hx : x ∈ S)
  (hux : connK ends L u x) :
-- imply
  ∃ i, i ∈ L \ K ∧ ∃ a b, a ∈ ends i ∧ b ∈ ends i ∧ a ∉ S ∧ b ∈ S := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_crossing_edge_mem_sdiff_of_connK hcross hu hx hux

/--
[edgeInside_compl_componentComplement_of_mem_edgeComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma edgeInside_compl_componentComplement_of_mem_edgeComponent_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (hi : i ∈ edgeComponent ends K u) :
-- imply
  edgeInsideK ends (StatMech.FrontierA.grahamComponentComplement ends K u)ᶜ i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.edgeInside_compl_componentComplement_of_mem_edgeComponent ends K u hi

/--
[mem_edgeComponent_iff_edgeInside_compl_componentComplement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_edgeComponent_iff_edgeInside_compl_componentComplement_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u : W}
  {i : I}
-- given
  (ends : I -> Sym2 W) :
-- imply
  i ∈ edgeComponent ends K u ↔ i ∈ K ∧ edgeInsideK ends (StatMech.FrontierA.grahamComponentComplement ends K u)ᶜ i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_edgeComponent_iff_edgeInside_compl_componentComplement ends K u

/--
[not_mem_ends_of_mem_sdiff_edgeComponent_of_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma not_mem_ends_of_mem_sdiff_edgeComponent_of_conn_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u v : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (hi : i ∈ K \ edgeComponent ends K u)
  (huv : connK ends K u v) :
-- imply
  v ∉ ends i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.not_mem_ends_of_mem_sdiff_edgeComponent_of_conn ends K u v hi huv

/--
[sources_inter_edgeComponent_and_sdiff_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sources_inter_edgeComponent_and_sdiff_eq_empty_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hDK : D ⊆ K)
  (hDsrc : sources ends D = ∅) :
-- imply
  sources ends (D ∩ edgeComponent ends K u) = ∅ ∧ sources ends (D \ edgeComponent ends K u) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_inter_edgeComponent_and_sdiff_eq_empty ends K D u hDK hDsrc

/--
[noCrossing_componentComplement_of_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma noCrossing_componentComplement_of_subset_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hDK : D ⊆ K) :
-- imply
  NoCrossingK ends D (StatMech.FrontierA.grahamComponentComplement ends K u) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.noCrossing_componentComplement_of_subset ends K D u hDK

/--
[sources_canonicalTransferUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sources_canonicalTransferUnion_eq
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
  sources ends (canonicalTransferUnion ends m k zero r.1.1) = {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_canonicalTransferUnion hloop hjk hkl r

/--
[sources_canonicalNormalRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sources_canonicalNormalRow_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  sources ends (canonicalNormalRow ends m k zero c.1.1) = {j, k} ∆ {k, l} := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_canonicalNormalRow hloop hjk hkl c

/--
[sources_canonicalNormalRow_symmDiff_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sources_canonicalNormalRow_symmDiff_eq_empty_eq
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
  sources ends (canonicalNormalRow ends m k zero c.1.1 ∆ canonicalNormalRow ends m k zero d.1.1) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_canonicalNormalRow_symmDiff_eq_empty hloop hjk hkl c d

/--
[sources_fourfold_canonicalTransferUnion_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sources_fourfold_canonicalTransferUnion_symmDiff_eq
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
  sources ends (canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 ∆ canonicalTransferUnion ends m k zero c.1.1 ∆ canonicalTransferUnion ends m k zero d.1.1) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_fourfold_canonicalTransferUnion_symmDiff hloop hjk hkl a b c d

/--
[sources_canonicalTransferUnion_symmDiff_eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sources_canonicalTransferUnion_symmDiff_eq_empty_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  sources ends (canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1) = ∅ := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sources_canonicalTransferUnion_symmDiff_eq_empty hloop hjk hkl a b

/--
[mem_canonicalTransferUnion_iff_rooted_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_canonicalTransferUnion_iff_rooted_endpoints_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  i ∈ canonicalTransferUnion ends m k zero c ↔ (i ∈ rowClass m c 0 ∧ ∀ x ∈ ends i, connK ends (rowClass m c 0) zero x) ∨ (i ∈ rowClass m c 1 ∧ ∀ x ∈ ends i, connK ends (rowClass m c 1) k x) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalTransferUnion_iff_rooted_endpoints ends m k zero c i

/--
[mem_canonicalTransferUnion_iff_rootComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_canonicalTransferUnion_iff_rootComponents_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  i ∈ canonicalTransferUnion ends m k zero c ↔ i ∈ edgeComponent ends (rowClass m c 0) zero ∨ i ∈ edgeComponent ends (rowClass m c 1) k := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalTransferUnion_iff_rootComponents ends m k zero c i

/--
[mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4)
  (hi : i ∈ canonicalTransferUnion ends m k zero c) :
-- imply
  i ∈ edgeComponent ends (rowClass m c 0) zero ↔ i ∈ rowClass m c 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_zeroRootComponent_iff_mem_rowZero_of_mem_canonicalTransferUnion ends m k zero c i hi

/--
[mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4)
  (hi : i ∈ canonicalTransferUnion ends m k zero c) :
-- imply
  i ∈ edgeComponent ends (rowClass m c 1) k ↔ i ∉ rowClass m c 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_kRootComponent_iff_not_mem_rowZero_of_mem_canonicalTransferUnion ends m k zero c i hi

/--
[canonicalTransferUnion_disjoint_nonrootRowZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalTransferUnion_disjoint_nonrootRowZero_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  Disjoint (canonicalTransferUnion ends m k zero c) (rowClass m c 0 \ edgeComponent ends (rowClass m c 0) zero) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferUnion_disjoint_nonrootRowZero ends m k zero c

/--
[canonicalTransferUnion_disjoint_nonrootRowOne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalTransferUnion_disjoint_nonrootRowOne_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  Disjoint (canonicalTransferUnion ends m k zero c) (rowClass m c 1 \ edgeComponent ends (rowClass m c 1) k) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferUnion_disjoint_nonrootRowOne ends m k zero c

/--
[canonicalTransferUnion_twoRootSpanning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalTransferUnion_twoRootSpanning_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  TwoRootSpanning ends (canonicalTransferUnion ends m k zero c) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferUnion_twoRootSpanning ends m k zero c

/--
[exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent_eq
  [Fintype I]
  [DecidableEq I]
  {K T : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (hkzero : connK ends K k zero)
  (hT : TwoRootSpanning ends T k zero)
  (hi : i ∈ K \ edgeComponent ends K zero)
  (hiT : i ∈ T) :
-- imply
  ∃ e, e ∈ T \ K ∧ ∃ a b, a ∈ ends e ∧ b ∈ ends e ∧ a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧ b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_twoRootSpanning_crossing_edge_of_mem_sdiff_edgeComponent ends K T k zero hkzero hT hi hiT

/--
[twoRootSpanning_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma twoRootSpanning_union_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {A B : Finset I}
  {u v : W}
-- given
  (hA : TwoRootSpanning ends A u v)
  (hB : TwoRootSpanning ends B u v) :
-- imply
  TwoRootSpanning ends (A ∪ B) u v := by
-- proof
  apply StatMech.GrahamGHS.FourColor.twoRootSpanning_union hA hB

/--
[rootSpanning_union_of_conn_of_twoRootSpanning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rootSpanning_union_of_conn_of_twoRootSpanning_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {K S : Finset I}
  {u v : W}
-- given
  (hK : RootSpanning ends K u)
  (huv : connK ends K u v)
  (hS : TwoRootSpanning ends S u v) :
-- imply
  RootSpanning ends (K ∪ S) u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rootSpanning_union_of_conn_of_twoRootSpanning hK huv hS

/--
[edgeComponent_rootSpanning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma edgeComponent_rootSpanning_eq
  [Fintype I]
  [DecidableEq I]
  {K : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W) :
-- imply
  RootSpanning ends (edgeComponent ends K u) u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.edgeComponent_rootSpanning ends K u

/--
[subset_edgeComponent_of_subset_of_rootSpanning_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma subset_edgeComponent_of_subset_of_rootSpanning_union_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hDK : D ⊆ K)
  (hroot : RootSpanning ends (edgeComponent ends K u ∪ D) u) :
-- imply
  D ⊆ edgeComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.subset_edgeComponent_of_subset_of_rootSpanning_union ends K D u hDK hroot

/--
[rootSpanning_union_of_edgeComponents_meet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rootSpanning_union_of_edgeComponents_meet_eq
  [Fintype I]
  [DecidableEq I]
  {E D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hE : RootSpanning ends E u)
  (hmeet : ∀ i ∈ D, ∀ x ∈ ends i, ∃ e ∈ D ∩ E, ∃ y ∈ ends e, connK ends D x y) :
-- imply
  RootSpanning ends (E ∪ D) u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rootSpanning_union_of_edgeComponents_meet ends E D u hE hmeet

/--
[subset_edgeComponent_of_subset_of_edgeComponents_meet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma subset_edgeComponent_of_subset_of_edgeComponents_meet_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hDK : D ⊆ K)
  (hmeet : ∀ i ∈ D, ∀ x ∈ ends i, ∃ e ∈ D ∩ edgeComponent ends K u, ∃ y ∈ ends e, connK ends D x y) :
-- imply
  D ⊆ edgeComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.subset_edgeComponent_of_subset_of_edgeComponents_meet ends K D u hDK hmeet

/--
[rootSpanning_union_of_everyEdgeComponentMeets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rootSpanning_union_of_everyEdgeComponentMeets_eq
  [Fintype I]
  [DecidableEq I]
  {E D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hE : RootSpanning ends E u)
  (hmeet : EveryEdgeComponentMeets ends D E) :
-- imply
  RootSpanning ends (E ∪ D) u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rootSpanning_union_of_everyEdgeComponentMeets ends E D u hE hmeet

/--
[subset_edgeComponent_of_subset_of_everyEdgeComponentMeets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma subset_edgeComponent_of_subset_of_everyEdgeComponentMeets_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hDK : D ⊆ K)
  (hmeet : EveryEdgeComponentMeets ends D (edgeComponent ends K u)) :
-- imply
  D ⊆ edgeComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.subset_edgeComponent_of_subset_of_everyEdgeComponentMeets ends K D u hDK hmeet

/--
[everyEdgeComponentMeets_edgeComponent_iff_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma everyEdgeComponentMeets_edgeComponent_iff_subset_eq
  [Fintype I]
  [DecidableEq I]
  {K D : Finset I}
  {u : W}
-- given
  (ends : I -> Sym2 W)
  (hDK : D ⊆ K) :
-- imply
  EveryEdgeComponentMeets ends D (edgeComponent ends K u) ↔ D ⊆ edgeComponent ends K u := by
-- proof
  apply StatMech.GrahamGHS.FourColor.everyEdgeComponentMeets_edgeComponent_iff_subset ends K D u hDK

/--
[mem_canonicalNormalRow_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_canonicalNormalRow_iff_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (c : ↑m -> Fin 4) :
-- imply
  i ∈ canonicalNormalRow ends m k zero c ↔ (i ∈ rowClass m c 0 ∧ i ∉ canonicalTransferUnion ends m k zero c) ∨ (i ∈ canonicalTransferUnion ends m k zero c ∧ i ∉ rowClass m c 0) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalNormalRow_iff ends m k zero c i

/--
[canonicalNormalRow_eq_rowClass_selfSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_eq_rowClass_selfSwap_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  canonicalNormalRow ends m k zero c = rowClass m (balancedSwap m (canonicalMiddleTransfer ends m c k zero) (canonicalOuterTransfer ends m c k zero) c) 0 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_eq_rowClass_selfSwap hloop hjk hkl hc

/--
[canonicalNormalRow_no_incident_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_no_incident_zero_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
-- imply
  ∀ i ∈ canonicalNormalRow ends m k zero c, zero ∉ ends i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_no_incident_zero hloop hjk hkl hc

/--
[mem_canonicalNormalRow_of_mem_k](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma mem_canonicalNormalRow_of_mem_k_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {c : ↑m -> Fin 4}
  {i : I}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hc : LeftPattern ends m {j, k} {k, l} k zero c)
  (him : i ∈ m)
  (hik : k ∈ ends i) :
-- imply
  i ∈ canonicalNormalRow ends m k zero c := by
-- proof
  apply StatMech.GrahamGHS.FourColor.mem_canonicalNormalRow_of_mem_k hloop hjk hkl hc him hik

/--
[rowClass_canonicalQuadrangleCompletion_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rowClass_canonicalQuadrangleCompletion_zero_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) 0 = rowClass m c.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_canonicalQuadrangleCompletion_zero hloop hjk hkl a b c

/--
[rowClass_canonicalQuadrangleCompletion_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rowClass_canonicalQuadrangleCompletion_one_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) 1 = rowClass m c.1.1 1 ∆ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_canonicalQuadrangleCompletion_one hloop hjk hkl a b c

/--
[rowClass_canonicalQuadrangleCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rowClass_canonicalQuadrangleCompletion_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
  {rho : Fin 2}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) rho = rowClass m c.1.1 rho ∆ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_canonicalQuadrangleCompletion hloop hjk hkl a b c rho

/--
[canonicalTranslatedRow_quadrangleCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalTranslatedRow_quadrangleCompletion_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  canonicalTranslatedRow ends m k zero a.1.1 c.1.1 = canonicalTranslatedRow ends m k zero b.1.1 (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTranslatedRow_quadrangleCompletion hloop hjk hkl a b c

/--
[rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
  {rho : Fin 2}
  {i : I}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hi : i ∉ rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) rho) :
-- imply
  (i ∈ rowClass m c.1.1 rho) ↔ i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.rowClass_pair_parity_of_not_mem_canonicalQuadrangleCompletion hloop hjk hkl a b c rho hi

/--
[fourfold_symmDiff_subset_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma fourfold_symmDiff_subset_union_eq
  [Fintype I]
  [DecidableEq I]
  {A B C D : Finset I} :
-- imply
  A ∆ B ∆ C ∆ D ⊆ ((A ∪ B) ∪ C) ∪ D := by
-- proof
  apply StatMech.GrahamGHS.FourColor.fourfold_symmDiff_subset_union A B C D

/--
[exists_other_mem_of_mem_of_not_mem_fourfold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_other_mem_of_mem_of_not_mem_fourfold_eq
  [Fintype I]
  [DecidableEq I]
  {A B C D : Finset I}
  {i : I}
-- given
  (hiA : i ∈ A)
  (hnot : i ∉ A ∆ B ∆ C ∆ D) :
-- imply
  i ∈ B ∨ i ∈ C ∨ i ∈ D := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_other_mem_of_mem_of_not_mem_fourfold A B C D i hiA hnot

/--
[atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {A B C D : Finset I}
  {i : I}
-- given
  (hi : i ∈ ((A ∪ B) ∪ C) ∪ D)
  (hnot : i ∉ A ∆ B ∆ C ∆ D) :
-- imply
  AtLeastTwoOfFour A B C D i := by
-- proof
  apply StatMech.GrahamGHS.FourColor.atLeastTwoOfFour_of_mem_union_of_not_mem_symmDiff A B C D i hi hnot

/--
[four_canonicalTransferUnion_twoRootSpanning](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma four_canonicalTransferUnion_twoRootSpanning_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (a b c d : ↑m -> Fin 4) :
-- imply
  TwoRootSpanning ends (((canonicalTransferUnion ends m k zero a ∪ canonicalTransferUnion ends m k zero b) ∪ canonicalTransferUnion ends m k zero c) ∪ canonicalTransferUnion ends m k zero d) k zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.four_canonicalTransferUnion_twoRootSpanning ends m k zero a b c d

/--
[exists_two_canonicalTransfers_at_failedCutCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_two_canonicalTransfers_at_failedCutCrossing_eq
  [Fintype I]
  [DecidableEq I]
  {m K : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (r s x y : ↑m -> Fin 4)
  (hkzero : connK ends K k zero)
  (hD : canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero s ∆ canonicalTransferUnion ends m k zero x ∆ canonicalTransferUnion ends m k zero y ⊆ K)
  (hi : i ∈ (canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero s ∆ canonicalTransferUnion ends m k zero x ∆ canonicalTransferUnion ends m k zero y) \ edgeComponent ends K zero) :
-- imply
  ∃ e, e ∈ (((canonicalTransferUnion ends m k zero r ∪ canonicalTransferUnion ends m k zero s) ∪ canonicalTransferUnion ends m k zero x) ∪ canonicalTransferUnion ends m k zero y) \ K ∧ (∃ a b, a ∈ ends e ∧ b ∈ ends e ∧ a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧ b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero) ∧ AtLeastTwoOfFour (canonicalTransferUnion ends m k zero r) (canonicalTransferUnion ends m k zero s) (canonicalTransferUnion ends m k zero x) (canonicalTransferUnion ends m k zero y) e := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_two_canonicalTransfers_at_failedCutCrossing ends m K k zero r s x y hkzero hD hi

/--
[exists_second_canonicalTransfer_at_failedCutCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_second_canonicalTransfer_at_failedCutCrossing_eq
  [Fintype I]
  [DecidableEq I]
  {m K : Finset I}
  {k zero : W}
  {i : I}
-- given
  (ends : I -> Sym2 W)
  (r s x y : ↑m -> Fin 4)
  (hkzero : connK ends K k zero)
  (hD : canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero s ∆ canonicalTransferUnion ends m k zero x ∆ canonicalTransferUnion ends m k zero y ⊆ K)
  (hi : i ∈ K \ edgeComponent ends K zero)
  (hir : i ∈ canonicalTransferUnion ends m k zero r) :
-- imply
  ∃ e, e ∈ canonicalTransferUnion ends m k zero r \ K ∧ (∃ a b, a ∈ ends e ∧ b ∈ ends e ∧ a ∉ StatMech.FrontierA.grahamComponentComplement ends K zero ∧ b ∈ StatMech.FrontierA.grahamComponentComplement ends K zero) ∧ (e ∈ canonicalTransferUnion ends m k zero s ∨ e ∈ canonicalTransferUnion ends m k zero x ∨ e ∈ canonicalTransferUnion ends m k zero y) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_second_canonicalTransfer_at_failedCutCrossing ends m K k zero r s x y hkzero hD hi hir

/--
[canonicalNormalRow_symmDiff_eq_of_translatedRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_symmDiff_eq_of_translatedRow_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r s x y : ↑m -> Fin 4)
  (hxy : canonicalTranslatedRow ends m k zero r x = canonicalTranslatedRow ends m k zero s y) :
-- imply
  canonicalNormalRow ends m k zero x ∆ canonicalNormalRow ends m k zero y = canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero s ∆ canonicalTransferUnion ends m k zero x ∆ canonicalTransferUnion ends m k zero y := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_symmDiff_eq_of_translatedRow_eq ends m k zero r s x y hxy

/--
[canonicalNormalRow_symmDiff_eq_pairDifferences_of_translatedRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_symmDiff_eq_pairDifferences_of_translatedRow_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r s x y : ↑m -> Fin 4)
  (hxy : canonicalTranslatedRow ends m k zero r x = canonicalTranslatedRow ends m k zero s y) :
-- imply
  canonicalNormalRow ends m k zero x ∆ canonicalNormalRow ends m k zero y = (canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero x) ∆ (canonicalTransferUnion ends m k zero s ∆ canonicalTransferUnion ends m k zero y) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_symmDiff_eq_pairDifferences_of_translatedRow_eq ends m k zero r s x y hxy

/--
[canonicalQuadrangleCompletion_normalRowDiscrepancy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_normalRowDiscrepancy_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1 canonicalNormalRow ends m k zero c.1.1 ∆ canonicalNormalRow ends m k zero d = canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 ∆ canonicalTransferUnion ends m k zero c.1.1 ∆ canonicalTransferUnion ends m k zero d := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_normalRowDiscrepancy hloop hjk hkl a b c

/--
[canonicalQuadrangleCompletion_nonrootRowZero_discrepancy_threeLabels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_nonrootRowZero_discrepancy_threeLabels_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
  {i : I}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hiD : i ∈ canonicalNormalRow ends m k zero c.1.1 ∆ canonicalNormalRow ends m k zero (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1))
  (hiK : i ∈ rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) 0 \ edgeComponent ends (rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) 0) zero) :
-- imply
  i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 ∆ canonicalTransferUnion ends m k zero c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_nonrootRowZero_discrepancy_threeLabels hloop hjk hkl a b c hiD hiK

/--
[canonicalQuadrangleCompletion_nonrootRowOne_discrepancy_threeLabels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalQuadrangleCompletion_nonrootRowOne_discrepancy_threeLabels_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
  {i : I}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hiD : i ∈ canonicalNormalRow ends m k zero c.1.1 ∆ canonicalNormalRow ends m k zero (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1))
  (hiK : i ∈ rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) 1 \ edgeComponent ends (rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) 1) k) :
-- imply
  i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1 ∆ canonicalTransferUnion ends m k zero c.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalQuadrangleCompletion_nonrootRowOne_discrepancy_threeLabels hloop hjk hkl a b c hiD hiK

/--
[canonicalTransferPairDifference_eq_translatedRow_symmDiff_normalRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalTransferPairDifference_eq_translatedRow_symmDiff_normalRow_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r x : ↑m -> Fin 4) :
-- imply
  canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero x = canonicalTranslatedRow ends m k zero r x ∆ canonicalNormalRow ends m k zero x := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalTransferPairDifference_eq_translatedRow_symmDiff_normalRow ends m k zero r x

/--
[canonicalNormalRow_sdiff_eq_of_component_meets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_sdiff_eq_of_component_meets_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {k zero : W}
  {K : Finset I}
-- given
  (ends : I -> Sym2 W)
  (x y : ↑m -> Fin 4)
  (hrow : canonicalNormalRow ends m k zero x ∆ canonicalNormalRow ends m k zero y ⊆ K)
  (hmeet : EveryEdgeComponentMeets ends (canonicalNormalRow ends m k zero x ∆ canonicalNormalRow ends m k zero y) (edgeComponent ends K zero)) :
-- imply
  canonicalNormalRow ends m k zero x \ edgeComponent ends K zero = canonicalNormalRow ends m k zero y \ edgeComponent ends K zero := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_sdiff_eq_of_component_meets ends m k zero K x y hrow hmeet

/--
[not_mem_symmDiff_iff_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma not_mem_symmDiff_iff_mem_iff_eq
  [Fintype I]
  [DecidableEq I]
  {A B : Finset I}
  {i : I} :
-- imply
  i ∉ A ∆ B ↔ (i ∈ A ↔ i ∈ B) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.not_mem_symmDiff_iff_mem_iff A B i

/--
[transfer_pair_parity_of_translatedRow_eq_of_root_incident](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma transfer_pair_parity_of_translatedRow_eq_of_root_incident_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s x y : leftMaskFiber ends m j k l zero p}
  {i : I}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hrs : canonicalTranslatedRow ends m k zero r.1.1 x.1.1 = canonicalTranslatedRow ends m k zero s.1.1 y.1.1)
  (him : i ∈ m)
  (hroot : k ∈ ends i ∨ zero ∈ ends i) :
-- imply
  (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆ canonicalTransferUnion ends m k zero s.1.1) ↔ i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆ canonicalTransferUnion ends m k zero y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.transfer_pair_parity_of_translatedRow_eq_of_root_incident hloop hjk hkl r s x y hrs him hroot

/--
[transfer_pair_parity_of_not_mem_total](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma transfer_pair_parity_of_not_mem_total_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {r s x y : leftMaskFiber ends m j k l zero p}
  {i : I}
-- given
  (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (him : i ∉ m) :
-- imply
  (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆ canonicalTransferUnion ends m k zero s.1.1) ↔ i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆ canonicalTransferUnion ends m k zero y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.transfer_pair_parity_of_not_mem_total hloop hjk hkl r s x y him

/--
[exists_opposite_badQuadrangle_of_coverage_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_opposite_badQuadrangle_of_coverage_card_le_eq
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
  (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b)
  (hcard : #(canonicalMaskOrbitCoverage ends m j k l zero p a) ≤ #(canonicalMaskOrbitCoverage ends m j k l zero p b)) :
-- imply
  ∃ d, d ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p b a := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_opposite_badQuadrangle_of_coverage_card_le hloop hjk hkl a b c hab hc hcard

/--
[canonicalCoverageExclusiveBadQuadrangle_typedData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalCoverageExclusiveBadQuadrangle_typedData_eq
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
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1 CanonicalMaskTransferOrbit ends m j k l zero p a c ∧ CanonicalMaskTransferOrbit ends m j k l zero p b c ∧ CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧ ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧ CanonicalTransferWorks ends m k zero b.1.1 d ∧ ((connK ends (rowClass m d 0) k zero ∧ sources ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧ sources ends (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) = ∅ ∧ Disjoint (canonicalTransferUnion ends m k zero d) (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero)) ∨ (connK ends (rowClass m d 1) k zero ∧ sources ends (edgeComponent ends (rowClass m d 1) k) = {k, l} ∧ sources ends (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) k) = ∅ ∧ Disjoint (canonicalTransferUnion ends m k zero d) (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) k))) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoverageExclusiveBadQuadrangle_typedData hloop hjk hkl a b c hab hc

/--
[canonicalCoverageExclusiveBadQuadrangle_nonroot_noRootIncidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalCoverageExclusiveBadQuadrangle_nonroot_noRootIncidence_eq
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
  (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles ends m j k l zero p a b) :
-- imply
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1 (∀ i ∈ rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero, k ∉ ends i ∧ zero ∉ ends i) ∨ (∀ i ∈ rowClass m d 1 \ edgeComponent ends (rowClass m d 1) k, k ∉ ends i ∧ zero ∉ ends i) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalCoverageExclusiveBadQuadrangle_nonroot_noRootIncidence hloop hjk hkl a b c hc

/--
[exists_transfer_symmDiff_eq_normalRow_symmDiff_of_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma exists_transfer_symmDiff_eq_normalRow_symmDiff_of_adjacent_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {x y : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y) :
-- imply
  ∃ r s : leftMaskFiber ends m j k l zero p, canonicalNormalRow ends m k zero x.1.1 ∆ canonicalNormalRow ends m k zero y.1.1 = canonicalTransferUnion ends m k zero r.1.1 ∆ canonicalTransferUnion ends m k zero s.1.1 ∆ canonicalTransferUnion ends m k zero x.1.1 ∆ canonicalTransferUnion ends m k zero y.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.exists_transfer_symmDiff_eq_normalRow_symmDiff_of_adjacent hloop hjk hkl x y hxy

/--
[sdiff_eq_sdiff_of_symmDiff_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma sdiff_eq_sdiff_of_symmDiff_subset_eq
  [Fintype I]
  [DecidableEq I]
  {A B E : Finset I}
-- given
  (hAB : A ∆ B ⊆ E) :
-- imply
  A \ E = B \ E := by
-- proof
  apply StatMech.GrahamGHS.FourColor.sdiff_eq_sdiff_of_symmDiff_subset A B E hAB

/--
[fourfold_symmDiff_subset_of_outside_pair_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma fourfold_symmDiff_subset_of_outside_pair_membership_eq
  [Fintype I]
  [DecidableEq I]
  {A B C D E : Finset I}
-- given
  (hout : ∀ i, i ∉ E -> (i ∈ A ∆ B ↔ i ∈ C ∆ D)) :
-- imply
  A ∆ B ∆ C ∆ D ⊆ E := by
-- proof
  apply StatMech.GrahamGHS.FourColor.fourfold_symmDiff_subset_of_outside_pair_membership A B C D E hout

/--
[canonicalNormalRow_symmDiff_subset_of_translatedRow_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_symmDiff_subset_of_translatedRow_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m K : Finset I}
  {k zero : W}
-- given
  (ends : I -> Sym2 W)
  (r s x y : ↑m -> Fin 4)
  (hrs : canonicalTranslatedRow ends m k zero r x = canonicalTranslatedRow ends m k zero s y)
  (hout : ∀ i, i ∉ K -> (i ∈ canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero s ↔ i ∈ canonicalTransferUnion ends m k zero x ∆ canonicalTransferUnion ends m k zero y)) :
-- imply
  canonicalNormalRow ends m k zero x ∆ canonicalNormalRow ends m k zero y ⊆ K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_symmDiff_subset_of_translatedRow_eq ends m K k zero r s x y hrs hout

/--
[canonicalNormalRow_symmDiff_subset_canonicalQuadrangleRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_symmDiff_subset_canonicalQuadrangleRow_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {a b c : leftMaskFiber ends m j k l zero p}
  {rho : Fin 2}
  {K : Finset I}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hK : K = rowClass m (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1) rho)
  (r s x y : ↑m -> Fin 4)
  (hrs : canonicalTranslatedRow ends m k zero r x = canonicalTranslatedRow ends m k zero s y)
  (href : ∀ i, i ∉ K -> (i ∈ canonicalTransferUnion ends m k zero r ∆ canonicalTransferUnion ends m k zero s ↔ i ∈ rowClass m c.1.1 rho))
  (hend : ∀ i, i ∉ K -> (i ∈ canonicalTransferUnion ends m k zero x ∆ canonicalTransferUnion ends m k zero y ↔ i ∈ canonicalTransferUnion ends m k zero a.1.1 ∆ canonicalTransferUnion ends m k zero b.1.1)) :
-- imply
  canonicalNormalRow ends m k zero x ∆ canonicalNormalRow ends m k zero y ⊆ K := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_symmDiff_subset_canonicalQuadrangleRow hloop hjk hkl a b c rho K hK r s x y hrs href hend

/--
[canonicalNormalRow_sdiff_eq_of_adjacent_of_outside_transfer_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_sdiff_eq_of_adjacent_of_outside_transfer_membership_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {E : Finset I}
  {x y : leftMaskFiber ends m j k l zero p}
-- given
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y)
  (hcancel : ∀ r s : leftMaskFiber ends m j k l zero p, canonicalTranslatedRow ends m k zero r.1.1 x.1.1 = canonicalTranslatedRow ends m k zero s.1.1 y.1.1 -> ∀ i, i ∉ E -> (i ∈ canonicalTransferUnion ends m k zero r.1.1 ∆ canonicalTransferUnion ends m k zero s.1.1 ↔ i ∈ canonicalTransferUnion ends m k zero x.1.1 ∆ canonicalTransferUnion ends m k zero y.1.1)) :
-- imply
  canonicalNormalRow ends m k zero x.1.1 \ E = canonicalNormalRow ends m k zero y.1.1 \ E := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_sdiff_eq_of_adjacent_of_outside_transfer_membership hloop hjk hkl E x y hxy hcancel

/--
[canonicalNormalRow_sdiff_eq_of_orbit_of_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_sdiff_eq_of_orbit_of_adjacent_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {E : Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hstep : ∀ x y : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferAdjacent ends m j k l zero p x y -> canonicalNormalRow ends m k zero x.1.1 \ E = canonicalNormalRow ends m k zero y.1.1 \ E)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalNormalRow ends m k zero c.1.1 \ E = canonicalNormalRow ends m k zero d.1.1 \ E := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_sdiff_eq_of_orbit_of_adjacent E hstep c d hcd

/--
[symmDiff_subset_union_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma symmDiff_subset_union_symmDiff_eq
  [Fintype I]
  [DecidableEq I]
  {A B C : Finset I} :
-- imply
  A ∆ C ⊆ (A ∆ B) ∪ (B ∆ C) := by
-- proof
  apply StatMech.GrahamGHS.FourColor.symmDiff_subset_union_symmDiff A B C

/--
[canonicalNormalRow_symmDiff_subset_of_orbit_of_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferComponentCut.lean)
-/
@[path]
private lemma canonicalNormalRow_symmDiff_subset_of_orbit_of_adjacent_eq
  [Fintype I]
  [DecidableEq I]
  {ends : I -> Sym2 W}
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {E : Finset I}
  {c d : leftMaskFiber ends m j k l zero p}
-- given
  (hstep : ∀ x y : leftMaskFiber ends m j k l zero p, CanonicalMaskTransferAdjacent ends m j k l zero p x y -> canonicalNormalRow ends m k zero x.1.1 ∆ canonicalNormalRow ends m k zero y.1.1 ⊆ E)
  (hcd : CanonicalMaskTransferOrbit ends m j k l zero p c d) :
-- imply
  canonicalNormalRow ends m k zero c.1.1 ∆ canonicalNormalRow ends m k zero d.1.1 ⊆ E := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalNormalRow_symmDiff_subset_of_orbit_of_adjacent E hstep c d hcd


-- created on 2026-10-23
