import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
open MeasureTheory StatMech StatMech.ConfigSpace StatMech.Percolation


/--
[ergodic_ae_const_of_shiftInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma ergodic_ae_const_of_shiftInvariant_eq
  [Group G]
  [MulAction G E]
  {μ : Measure (ConfigSpace E)}
  [IsProbabilityMeasure μ]
  [Countable β]
  [MeasurableSpace β]
  [MeasurableSingletonClass β]
  {f : ConfigSpace E → β}
-- given
  (herg : IsErgodic (G := G) μ)
  (hf : Measurable f)
  (hinv : ∀ (g : G) (ω : ConfigSpace E), f (shift g ω) = f ω) :
-- imply
  ∃ k : β, μ {ω | f ω = k} = 1 := by
-- proof
  apply StatMech.ConfigSpace.ergodic_ae_const_of_shiftInvariant herg f hf hinv

/--
[smul_sym2_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma smul_sym2_mk_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {x y : Site d} :
-- imply
  g • s(x, y) = s(g • x, g • y) := by
-- proof
  apply StatMech.Percolation.smul_sym2_mk g x y

/--
[smul_site_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma smul_site_apply_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {x : Site d}
  {i : Fin d} :
-- imply
  (g • x) i = Multiplicative.toAdd g i + x i := by
-- proof
  apply StatMech.Percolation.smul_site_apply g x i

/--
[hyper_adj_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma hyper_adj_smul_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {x y : Site d} :
-- imply
  (hypercubicLattice d).Adj (g • x) (g • y) ↔ (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.Percolation.hyper_adj_smul g x y

/--
[shift_apply_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma shift_apply_smul_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  (shift g ω) s(g • x, g • y) = ω s(x, y) := by
-- proof
  apply StatMech.Percolation.shift_apply_smul g ω x y

/--
[openSubgraph_adj_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma openSubgraph_adj_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  (openSubgraph d (shift g ω)).Adj (g • x) (g • y) ↔ (openSubgraph d ω).Adj x y := by
-- proof
  apply StatMech.Percolation.openSubgraph_adj_shift g ω x y

/--
[translateHomInv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma translateHomInv_apply_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {a : Site d} :
-- imply
  translateHomInv g ω a = g⁻¹ • a := by
-- proof
  apply StatMech.Percolation.translateHomInv_apply g ω a

/--
[connected_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma connected_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  Connected d (shift g ω) (g • x) (g • y) ↔ Connected d ω x y := by
-- proof
  apply StatMech.Percolation.connected_shift g ω x y

/--
[cluster_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma cluster_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  cluster d (shift g ω) (g • x) = (fun y => g • y) '' (cluster d ω x) := by
-- proof
  apply StatMech.Percolation.cluster_shift g ω x

/--
[smul_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma smul_injective_eq
  {d : ℕ}
  {g : Multiplicative (Site d)} :
-- imply
  Function.Injective (fun y : Site d => g • y) := by
-- proof
  apply StatMech.Percolation.smul_injective g

/--
[image_smul_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma image_smul_injective_eq
  {d : ℕ}
  {g : Multiplicative (Site d)} :
-- imply
  Function.Injective (fun C : Set (Site d) => (fun y => g • y) '' C) := by
-- proof
  apply StatMech.Percolation.image_smul_injective g

/--
[infiniteClusters_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma infiniteClusters_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  infiniteClusters d (shift g ω) = (fun C => (fun y => g • y) '' C) '' (infiniteClusters d ω) := by
-- proof
  apply StatMech.Percolation.infiniteClusters_shift g ω

/--
[numInfiniteClusters_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma numInfiniteClusters_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  numInfiniteClusters d (shift g ω) = numInfiniteClusters d ω := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_shift g ω

/--
[measurableSet_openAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma measurableSet_openAdj_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x y} := by
-- proof
  apply StatMech.Percolation.measurableSet_openAdj x y

/--
[measurableSet_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma measurableSet_isChain_eq
  {d : ℕ}
  {l : List (Site d)} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | List.IsChain (openSubgraph d ω).Adj l} := by
-- proof
  apply StatMech.Percolation.measurableSet_isChain l

/--
[connected_iff_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma connected_iff_chain_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  Connected d ω x y ↔ ∃ l : List (Site d), ∃ h : (x :: l) ≠ [], List.IsChain (openSubgraph d ω).Adj (x :: l) ∧ (x :: l).getLast h = y := by
-- proof
  apply StatMech.Percolation.connected_iff_chain ω x y

/--
[measurableSet_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma measurableSet_connected_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | Connected d ω x y} := by
-- proof
  apply StatMech.Percolation.measurableSet_connected x y

/--
[finite_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma finite_subset_box_eq
  {d : ℕ}
  {S : Set (Site d)}
-- given
  (hS : S.Finite) :
-- imply
  ∃ n, S ⊆ box d n := by
-- proof
  apply StatMech.Percolation.finite_subset_box S hS

/--
[cluster_infinite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma cluster_infinite_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  (cluster d ω x).Infinite ↔ ∀ n : ℕ, ∃ y, y ∉ box d n ∧ Connected d ω x y := by
-- proof
  apply StatMech.Percolation.cluster_infinite_iff ω x

/--
[measurableSet_clusterInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma measurableSet_clusterInfinite_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d ω x).Infinite} := by
-- proof
  apply StatMech.Percolation.measurableSet_clusterInfinite x

/--
[exists_encode_min](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma exists_encode_min_eq
  {d : ℕ}
  {S : Set (Site d)}
-- given
  (hne : S.Nonempty) :
-- imply
  ∃ x ∈ S, ∀ y ∈ S, Encodable.encode x ≤ Encodable.encode y := by
-- proof
  apply StatMech.Percolation.exists_encode_min S hne

/--
[image_cluster_repSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma image_cluster_repSet_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  (fun x => cluster d ω x) '' (repSet d ω) = infiniteClusters d ω := by
-- proof
  apply StatMech.Percolation.image_cluster_repSet ω

/--
[injOn_cluster_repSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma injOn_cluster_repSet_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  Set.InjOn (fun x => cluster d ω x) (repSet d ω) := by
-- proof
  apply StatMech.Percolation.injOn_cluster_repSet ω

/--
[numInfiniteClusters_eq_repSet_encard](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma numInfiniteClusters_eq_repSet_encard_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))} :
-- imply
  numInfiniteClusters d ω = (repSet d ω).encard := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_eq_repSet_encard ω

/--
[measurableSet_repSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma measurableSet_repSet_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | x ∈ repSet d ω} := by
-- proof
  apply StatMech.Percolation.measurableSet_repSet x

/--
[measurable_numInfiniteClusters](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma measurable_numInfiniteClusters_eq
  {d : ℕ} :
-- imply
  Measurable (numInfiniteClusters d) := by
-- proof
  apply StatMech.Percolation.measurable_numInfiniteClusters

/--
[numInfiniteClusters_ae_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeane.lean)
-/
@[path]
private lemma numInfiniteClusters_ae_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (herg : IsErgodic (G := Multiplicative (Site d)) μ) :
-- imply
  ∃ k : ℕ∞, μ {ω | numInfiniteClusters d ω = k} = 1 := by
-- proof
  apply StatMech.Percolation.numInfiniteClusters_ae_const μ herg


-- created on 2026-10-23
