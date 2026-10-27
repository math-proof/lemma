import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bc75_collapseFiber_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_collapseFiber_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {x y : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c)
  (hx : x ∈ bc61_boxAround d L y) :
-- imply
  bc75_collapseFiber ω L R c x = y := by
-- proof
  apply StatMech.Walls.bc75_collapseFiber_eq hy hx

/--
[bc75_collapseFiber_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_collapseFiber_id_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {x : Site d}
-- given
  (hx : ∀ y ∈ bc73_fiber ω L R c, x ∉ bc61_boxAround d L y) :
-- imply
  bc75_collapseFiber ω L R c x = x := by
-- proof
  apply StatMech.Walls.bc75_collapseFiber_id hx

/--
[bc75_collapseFiber_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_collapseFiber_center_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c) :
-- imply
  bc75_collapseFiber ω L R c y = y := by
-- proof
  apply StatMech.Walls.bc75_collapseFiber_center hy

/--
[bc75_collapseFiber_mem_box_of_eq_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_collapseFiber_mem_box_of_eq_center_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {x y : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c)
  (hxy : bc75_collapseFiber ω L R c x = y) :
-- imply
  x ∈ bc61_boxAround d L y := by
-- proof
  apply StatMech.Walls.bc75_collapseFiber_mem_box_of_eq_center hy hxy

/--
[bc75_arm_adjacent_hub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_arm_adjacent_hub_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y a : Site d}
-- given
  (hy : y ∈ bc73_fiber ω L R c)
  (hinc : bc67_GnIncident ω L y a)
  (hane : bc75_collapseFiber ω L R c a = a)
  (hay : a ≠ y) :
-- imply
  (bc75_fiberQuot ω L R c).Adj y a := by
-- proof
  apply StatMech.Walls.bc75_arm_adjacent_hub hy hinc hane hay

/--
[bc75_fiberQuot_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_fiberQuot_adj_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {u v : Site d} :
-- imply
  (bc75_fiberQuot ω L R c).Adj u v ↔ u ≠ v ∧ ∃ p q, bc75_collapseFiber ω L R c p = u ∧ bc75_collapseFiber ω L R c q = v ∧ (openSubgraph d ω).Adj p q := by
-- proof
  apply StatMech.Walls.bc75_fiberQuot_adj_iff

/--
[bc75_gnCut_of_doubleInduce](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_gnCut_of_doubleInduce_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
  {S : Set (Site d)}
  {a₁ a₂ : (↑S : Type)}
-- given
  (hyS : y ∈ S)
  (h0 : a₁ ≠ ⟨y, hyS⟩)
  (h1 : a₂ ≠ ⟨y, hyS⟩)
  (h : (((bc75_fiberQuot ω L R c).induce S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨a₁, by simpa using h0⟩ ⟨a₂, by simpa using h1⟩) :
-- imply
  ((bc75_fiberQuot ω L R c).induce ({y}ᶜ : Set (Site d))).Reachable ⟨(a₁ : Site d), by simpa using fun hh => h0 (Subtype.ext hh)⟩ ⟨(a₂ : Site d), by simpa using fun hh => h1 (Subtype.ext hh)⟩ := by
-- proof
  apply StatMech.Walls.bc75_gnCut_of_doubleInduce hyS h0 h1 h

/--
[bc75_spanForest_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_spanForest_acyclic_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)] :
-- imply
  (bc75_spanForest ω L R c S).IsAcyclic := by
-- proof
  apply StatMech.Walls.bc75_spanForest_acyclic ω L R c S

/--
[bc75_spanForest_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_spanForest_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)] :
-- imply
  bc75_spanForest ω L R c S ≤ bc75_fiberQuotBox ω L R c S := by
-- proof
  apply StatMech.Walls.bc75_spanForest_le ω L R c S

/--
[bc75_spanForest_reachable_of](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_spanForest_reachable_of_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {u v : (↑S : Type)}
-- given
  (h : (bc75_fiberQuotBox ω L R c S).Reachable u v) :
-- imply
  (bc75_spanForest ω L R c S).Reachable u v := by
-- proof
  apply StatMech.Walls.bc75_spanForest_reachable_of ω L R c S h

/--
[bc75_deg3_in_spanForest_of_gnCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_deg3_in_spanForest_of_gnCut_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {y : Site d}
  {S : Set (Site d)}
  [Fintype (↑S : Type)]
  {v₁ v₂ v₃ : (↑S : Type)}
-- given
  (hyS : y ∈ S)
  (hadj₁ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₁)
  (hadj₂ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₂)
  (hadj₃ : (bc75_fiberQuotBox ω L R c S).Adj ⟨y, hyS⟩ v₃)
  (hcut₁₂ : ¬ ((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩ ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩)
  (hcut₁₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₁, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₁).symm⟩ ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩)
  (hcut₂₃ : ¬ ((bc75_fiberQuotBox ω L R c S).induce ({(⟨y, hyS⟩ : (↑S : Type))}ᶜ : Set (↑S : Type))).Reachable ⟨v₂, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₂).symm⟩ ⟨v₃, by simpa using ((bc75_fiberQuotBox ω L R c S).ne_of_adj hadj₃).symm⟩) :
-- imply
  3 ≤ (bc75_spanForest ω L R c S).degree ⟨y, hyS⟩ := by
-- proof
  apply StatMech.Walls.bc75_deg3_in_spanForest_of_gnCut ω L R c hyS hadj₁ hadj₂ hadj₃ hcut₁₂ hcut₁₃ hcut₂₃

/--
[bc75_fiberForest_of_gnTrifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_fiberForest_of_gnTrifData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  bc74_FiberForest ω L R c := by
-- proof
  apply StatMech.Walls.bc75_fiberForest_of_gnTrifData ω L R c h

/--
[bc75_fiber_count_of_gnTrifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_fiber_count_of_gnTrifData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
-- given
  (h : bc75_FiberGnTrifData ω L R c) :
-- imply
  (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R := by
-- proof
  apply StatMech.Walls.bc75_fiber_count_of_gnTrifData ω L R c h

/--
[bc75_sublatticeForest_of_gnTrifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_sublatticeForest_of_gnTrifData_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
-- given
  (h : ∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc75_sublatticeForest_of_gnTrifData ω L R h

/--
[bc75_emptyFiber_collapse_id](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_emptyFiber_collapse_id_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {x : Site d}
-- given
  (hempty : bc73_fiber ω L R c = ∅) :
-- imply
  bc75_collapseFiber ω L R c x = x := by
-- proof
  apply StatMech.Walls.bc75_emptyFiber_collapse_id ω L R c hempty x

/--
[bc75_emptyFiber_box_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_emptyFiber_box_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {z₀ z₁ : Site d}
-- given
  (hempty : bc73_fiber ω L R c = ∅)
  (hopen : (openSubgraph d ω).Adj z₀ z₁)
  (hz₀ : z₀ ∈ ({z₀, z₁} : Set (Site d)))
  (hz₁ : z₁ ∈ ({z₀, z₁} : Set (Site d))) :
-- imply
  (bc75_fiberQuotBox ω L R c ({z₀, z₁} : Set (Site d))).Adj ⟨z₀, hz₀⟩ ⟨z₁, hz₁⟩ := by
-- proof
  apply StatMech.Walls.bc75_emptyFiber_box_adj ω L R c hempty hopen hz₀ hz₁

/--
[bc75_fiberGnTrifData_of_emptyFiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_fiberGnTrifData_of_emptyFiber_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {c : Fin d → Fin (2 * L + 1)}
  {z₀ z₁ : Site d}
-- given
  (hempty : bc73_fiber ω L R c = ∅)
  (hz₀b : z₀ ∈ vertexBoundary d R)
  (hz₁b : z₁ ∈ vertexBoundary d R)
  (hopen : (openSubgraph d ω).Adj z₀ z₁) :
-- imply
  bc75_FiberGnTrifData ω L R c := by
-- proof
  apply StatMech.Walls.bc75_fiberGnTrifData_of_emptyFiber ω L R c hempty hz₀b hz₁b hopen

/--
[bc75_sublatticeForest_of_noTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_sublatticeForest_of_noTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {z₀ z₁ : Site d}
-- given
  (hz₀b : z₀ ∈ vertexBoundary d R)
  (hz₁b : z₁ ∈ vertexBoundary d R)
  (hopen : (openSubgraph d ω).Adj z₀ z₁)
  (hno : bc61_coarseTrifFinset ω L R = ∅) :
-- imply
  bc73_SublatticeForest ω L R := by
-- proof
  apply StatMech.Walls.bc75_sublatticeForest_of_noTrif ω L R hz₀b hz₁b hopen hno

/--
[bc75_bk_count_closed_of_gnTrifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_bk_count_closed_of_gnTrifData_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
  {L : ℕ}
-- given
  (hd : 1 ≤ d)
  (hexp : ∀ R : ℕ, ((boxFinsetBK d R).card : ℝ≥0∞) * μ {ω | bc61_IsCoarseTrifurcation ω L 0} = ∫⁻ ω, (bc61_coarseTcount ω L R : ℝ≥0∞) ∂μ)
  (hData : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) (c : Fin d → Fin (2 * L + 1)), bc75_FiberGnTrifData ω L R c)
  (hexist : bc61_CoarseTrifExistence μ L) :
-- imply
  μ {ω | numInfiniteClusters d ω = ⊤} = 0 := by
-- proof
  apply StatMech.Walls.bc75_bk_count_closed_of_gnTrifData μ hd L hexp hData hexist

/--
[bc75_upperLines_openBoundaryEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_upperLines_openBoundaryEdge_eq
  {d : ℕ}
  {R : ℕ}
-- given
  (hR : 1 ≤ R) :
-- imply
  (bc57_pt 0 (R : ℤ) ∈ vertexBoundary 2 R) ∧ (bc57_pt 1 (R : ℤ) ∈ vertexBoundary 2 R) ∧ (openSubgraph 2 bc60_upperLines).Adj (bc57_pt 0 (R : ℤ)) (bc57_pt 1 (R : ℤ)) := by
-- proof
  apply StatMech.Walls.bc75_upperLines_openBoundaryEdge hR

/--
[bc75_upperLines_emptyFiber_gnTrifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_upperLines_emptyFiber_gnTrifData_eq
  {d : ℕ}
  {L R : ℕ}
  {c : Fin 2 → Fin (2 * L + 1)}
-- given
  (hR : 1 ≤ R)
  (hempty : bc73_fiber bc60_upperLines L R c = ∅) :
-- imply
  bc75_FiberGnTrifData bc60_upperLines L R c := by
-- proof
  apply StatMech.Walls.bc75_upperLines_emptyFiber_gnTrifData hR c hempty

/--
[bc75_upperLines_gnCut_needs_buffer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_upperLines_gnCut_needs_buffer_eq
  {d : ℕ}
  {L : ℕ} :
-- imply
  Disjoint (bc61_boxAround 2 L (0 : Site 2)) (bc61_boxAround 2 L (bc57_pt (2 * (L : ℤ) + 1) 0)) ∧ Connected 2 bc60_upperLines (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt (2 * (L : ℤ) + 1 + ((L : ℤ) + 1)) 1) := by
-- proof
  apply StatMech.Walls.bc75_upperLines_gnCut_needs_buffer L

/--
[bc75_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc75spanningtree.lean)
-/
@[path]
private lemma bc75_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)) (S : Set (Site d)) (_ : Fintype (↑S : Type)), (bc75_spanForest ω L R c S).IsAcyclic) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (c : Fin d → Fin (2 * L + 1)), bc75_FiberGnTrifData ω L R c → (bc73_fiber ω L R c).card ≤ boxSV_boundaryCard d R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), (∀ c : Fin d → Fin (2 * L + 1), bc75_FiberGnTrifData ω L R c) → bc73_SublatticeForest ω L R) := by
-- proof
  apply StatMech.Walls.bc75_status


-- created on 2026-10-23
