import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.FKInterfaceSubadd
open SimpleGraph Filter Topology StatMech StatMech.FK


/--
[fis_combine_false_of_interface](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_combine_false_of_interface_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
  {e : Sym2 (V ⊕ W)}
-- given
  (hci : fis_CrossInterface G H K)
  (he : e ∈ fis_interface G H K) :
-- imply
  fsm_combine σ τ e = false := by
-- proof
  apply StatMech.FK.fis_combine_false_of_interface hci σ τ he

/--
[fis_openSub_combine_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_openSub_combine_eq_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  openSub K (fsm_combine σ τ) = openSub (G ⊕g H) (fsm_combine σ τ) := by
-- proof
  apply StatMech.FK.fis_openSub_combine_eq hci σ τ

/--
[fis_numClusters_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_numClusters_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  numClusters K (fsm_combine σ τ) = numClusters G σ + numClusters H τ := by
-- proof
  apply StatMech.FK.fis_numClusters_combine hci σ τ

/--
[fis_sum_edgeFinset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_sum_edgeFinset_subset_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  (G ⊕g H).edgeFinset ⊆ K.edgeFinset := by
-- proof
  apply StatMech.FK.fis_sum_edgeFinset_subset hci

/--
[fis_edgeFinset_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_edgeFinset_eq_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  K.edgeFinset = (G ⊕g H).edgeFinset ∪ fis_interface G H K := by
-- proof
  apply StatMech.FK.fis_edgeFinset_eq hci

/--
[fis_edgeProduct_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_edgeProduct_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {p : ℝ}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  edgeProduct K p (fsm_combine σ τ) = (1 - p) ^ (fis_interface G H K).card * (edgeProduct G p σ * edgeProduct H p τ) := by
-- proof
  apply StatMech.FK.fis_edgeProduct_combine hci p σ τ

/--
[fis_fkWeight_combine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_fkWeight_combine_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {p q : ℝ}
  {σ : Sym2 V → Bool}
  {τ : Sym2 W → Bool}
-- given
  (hci : fis_CrossInterface G H K) :
-- imply
  fkWeight K p q (fsm_combine σ τ) = (1 - p) ^ (fis_interface G H K).card * (fkWeight G p q σ * fkWeight H p q τ) := by
-- proof
  apply StatMech.FK.fis_fkWeight_combine hci p q σ τ

/--
[fis_fkZ_interface_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_fkZ_interface_ge_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  (1 - p) ^ (fis_interface G H K).card * (fkZ G p q * fkZ H p q) ≤ fkZ K p q := by
-- proof
  apply StatMech.FK.fis_fkZ_interface_ge hci hp hp1 hq

/--
[fis_neglog_interface_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_neglog_interface_le_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G H K}
  {p q : ℝ}
-- given
  (hci : fis_CrossInterface G H K)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  - Real.log (fkZ K p q) ≤ - Real.log (fkZ G p q) + - Real.log (fkZ H p q) - (fis_interface G H K).card * Real.log (1 - p) := by
-- proof
  apply StatMech.FK.fis_neglog_interface_le hci hp hp1 hq

/--
[fis_subadditive_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_subadditive_of_bounded_eq
  {u : ℕ → ℝ}
  {C : ℝ}
-- given
  (hC : 0 ≤ C)
  (hu : ∀ m n, u (m + n) ≤ u m + u n + C) :
-- imply
  Subadditive (fun n => u n + C) := by
-- proof
  apply StatMech.FK.fis_subadditive_of_bounded hC hu

/--
[fis_interfaceData_of_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_interfaceData_of_bounded_eq
  {V : ℕ → Type*}
  [∀ n, Fintype (V n)]
  [∀ n, DecidableEq (V n)]
  [∀ n, DecidableRel (Gn n).Adj]
  {q : ℝ}
  {t : ℝ}
  {C : ℝ}
  {κ : ℝ}
-- given
  (Gn : ∀ n, SimpleGraph (V n))
  (hC : 0 ≤ C)
  (hglue : ∀ m n, - Real.log (fkZ (Gn (m + n)) (fsc_logistic t) q) ≤ - Real.log (fkZ (Gn m) (fsc_logistic t) q) + - Real.log (fkZ (Gn n) (fsc_logistic t) q) + C)
  (hbdd : BddBelow (Set.range fun n => (- Real.log (fkZ (Gn n) (fsc_logistic t) q) + C) / n))
  (hκ : κ ≠ 0)
  (he : Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ)) :
-- imply
  ∃ (c : ℕ → ℝ) (κ' : ℝ), Subadditive (fun n => - Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n) ∧ BddBelow (Set.range fun n => (- Real.log (fkZ (Gn n) (fsc_logistic t) q) + c n) / n) ∧ Tendsto (fun n => c n / n) atTop (𝓝 0) ∧ κ' ≠ 0 ∧ Tendsto (fun n => ((Gn n).edgeFinset.card : ℝ) / n) atTop (𝓝 κ') := by
-- proof
  apply StatMech.FK.fis_interfaceData_of_bounded Gn q t C hC hglue hbdd κ hκ he

/--
[fis_boxInterfaceData_of_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_boxInterfaceData_of_split_eq
  {d : ℕ}
  {t : ℝ}
-- given
  (hsplit : fis_UniformBoxSplit d t) :
-- imply
  bfd_FKInterfaceData d t := by
-- proof
  apply StatMech.FK.fis_boxInterfaceData_of_split t hsplit

/--
[fis_gluingBound_of_crossSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_gluingBound_of_crossSplit_eq
  {d : ℕ}
  {t : ℝ}
  {m n : ℕ}
  {K : SimpleGraph (boxVerts d m ⊕ boxVerts d n)}
  [DecidableRel K.Adj]
  {φ : boxGraph d (m + n) ≃g K}
-- given
  (hci : fis_CrossInterface (boxGraph d m) (boxGraph d n) K) :
-- imply
  - Real.log (fkZ (boxGraph d (m + n)) (fsc_logistic t) 2) ≤ - Real.log (fkZ (boxGraph d m) (fsc_logistic t) 2) + - Real.log (fkZ (boxGraph d n) (fsc_logistic t) 2) + (fis_interface (boxGraph d m) (boxGraph d n) K).card * (- Real.log (1 - fsc_logistic t)) := by
-- proof
  apply StatMech.FK.fis_gluingBound_of_crossSplit t m n K hci φ

/--
[fis_fk_uniqueness_of_boxSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_fk_uniqueness_of_boxSplit_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hsplit : ∀ t, fis_UniformBoxSplit d t)
  (hfreeBulk : ubd_FreeUniformBulkDeviation (d := d) N)
  (hwiredBulk : ubd_WiredUniformBulkDeviation (d := d) N) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.fis_fk_uniqueness_of_boxSplit hd N eb hEbox hsplit hfreeBulk hwiredBulk

/--
[fis_boundedGluing_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_boundedGluing_satisfiable_eq
  {d : ℕ} :
-- imply
  ∃ (u : ℕ → ℝ) (e : ℕ → ℝ) (C κ : ℝ), 0 ≤ C ∧ κ ≠ 0 ∧ (∀ m n, u (m + n) ≤ u m + u n + C) ∧ BddBelow (Set.range fun n => (u n + C) / n) ∧ Tendsto (fun n => e n / n) atTop (𝓝 κ) := by
-- proof
  apply StatMech.FK.fis_boundedGluing_satisfiable

/--
[fis_crossInterface_satisfiable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKInterfaceSubadd.lean)
-/
@[path]
private lemma fis_crossInterface_satisfiable_eq
  {d : ℕ}
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W] :
-- imply
  fis_CrossInterface (⊥ : SimpleGraph V) (⊥ : SimpleGraph W) (⊥ : SimpleGraph (V ⊕ W)) := by
-- proof
  apply StatMech.FK.fis_crossInterface_satisfiable


-- created on 2026-10-23
