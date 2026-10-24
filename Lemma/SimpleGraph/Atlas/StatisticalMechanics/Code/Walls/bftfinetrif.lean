import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bftfinetrif
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bft_boxAround_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_boxAround_zero_eq
  {d : ℕ}
  {y : Site d} :
-- imply
  bc61_boxAround d 0 y = {y} := by
-- proof
  apply StatMech.Walls.bft_boxAround_zero y

/--
[bft_contractedLattice_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_contractedLattice_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bc67_contractedLattice ω 0 x = bkg_deleteVertex (openSubgraph d ω) x := by
-- proof
  apply StatMech.Walls.bft_contractedLattice_zero ω x

/--
[bft_deleteVertex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_deleteVertex_le_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bkg_deleteVertex (openSubgraph d ω) x ≤ openSubgraph d ω := by
-- proof
  apply StatMech.Walls.bft_deleteVertex_le ω x

/--
[bft_gnIncident_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_gnIncident_zero_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d} :
-- imply
  bc67_GnIncident ω 0 x a ↔ (openSubgraph d ω).Adj x a := by
-- proof
  apply StatMech.Walls.bft_gnIncident_zero ω x a

/--
[bft_fineTrif_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_fineTrif_iff_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  bft_FineTrif ω x ↔ ∃ a₁ a₂ a₃ : Site d, ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧ ((cluster d (removeSites {x} ω) a₁).Infinite ∧ (cluster d (removeSites {x} ω) a₂).Infinite ∧ (cluster d (removeSites {x} ω) a₃).Infinite) ∧ (¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₂ ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₃ ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₂ a₃) := by
-- proof
  apply StatMech.Walls.bft_fineTrif_iff ω x

/--
[bft_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_separation_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
-- given
  (h : bft_FineTrif ω x) :
-- imply
  ∃ a₁ a₂ a₃ : Site d, a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₂ ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₃ ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₂ a₃ := by
-- proof
  apply StatMech.Walls.bft_separation ω h

/--
[bft_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_deg3_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {T : SimpleGraph {v // v ∈ S}}
  [DecidableRel T.Adj]
  {hub : {v // v ∈ S}}
  {a₁ a₂ a₃ : {v // v ∈ S}}
-- given
  (hTH : T ≤ bfct_restrict (openSubgraph d ω) S)
  (hTconn : T.Connected)
  (h : bft_FineTrif ω (hub : Site d))
  (he₁ : (a₁ : Site d) ≠ (hub : Site d))
  (he₂ : (a₂ : Site d) ≠ (hub : Site d))
  (he₃ : (a₃ : Site d) ≠ (hub : Site d))
  (hs₁₂ : ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₂ : Site d))
  (hs₁₃ : ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₃ : Site d))
  (hs₂₃ : ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₂ : Site d) (a₃ : Site d)) :
-- imply
  3 ≤ T.degree hub := by
-- proof
  apply StatMech.Walls.bft_deg3 ω hTH hTconn h he₁ he₂ he₃ hs₁₂ hs₁₃ hs₂₃

/--
[bft_armRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_armRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d}
-- given
  (hinf : (cluster d (removeSites ({x} : Finset (Site d)) ω) a).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = a ∧ Function.Injective r ∧ (∀ k, (bkg_deleteVertex (openSubgraph d ω) x).Adj (r k) (r (k + 1))) ∧ (∀ k, (bkg_deleteVertex (openSubgraph d ω) x).Reachable a (r k)) := by
-- proof
  apply StatMech.Walls.bft_armRay ω x a hinf

/--
[bft_arm_crosses_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_arm_crosses_boundary_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x a : Site d}
  {R : ℕ}
-- given
  (hR : 1 ≤ R)
  (haR : a ∈ box d R)
  (hinf : (cluster d (removeSites ({x} : Finset (Site d)) ω) a).Infinite) :
-- imply
  ∃ b : Site d, (bkg_deleteVertex (openSubgraph d ω) x).Reachable a b ∧ b ∈ vertexBoundary d R := by
-- proof
  apply StatMech.Walls.bft_arm_crosses_boundary ω x a R hR haR hinf

/--
[bft_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_count_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {T : SimpleGraph {v // v ∈ S}}
  [DecidableRel T.Adj]
  [Fintype ι]
-- given
  (hTH : T ≤ bfct_restrict (openSubgraph d ω) S)
  (hT : T.IsTree)
  (f : ι → {v // v ∈ S})
  (hf : Function.Injective f)
  (harm : ∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, (a₁ : Site d) ≠ (f i : Site d) ∧ (a₂ : Site d) ≠ (f i : Site d) ∧ (a₃ : Site d) ≠ (f i : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₂ : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₃ : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₂ : Site d) (a₃ : Site d))
  (B : Finset {v // v ∈ S})
  (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
-- imply
  Fintype.card ι ≤ B.card := by
-- proof
  apply StatMech.Walls.bft_count ω S hTH hT f hf harm B hleaf

/--
[bft_count_hyp_of_fineTrif](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_count_hyp_of_fineTrif_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {hub : {v // v ∈ S}}
-- given
  (h : bft_FineTrif ω (hub : Site d))
  (hmem : ∀ a₁ a₂ a₃ : Site d, ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable a₁ a₂ → ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable a₁ a₃ → ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable a₂ a₃ → a₁ ∈ S ∧ a₂ ∈ S ∧ a₃ ∈ S) :
-- imply
  ∃ a₁ a₂ a₃ : {v // v ∈ S}, (a₁ : Site d) ≠ (hub : Site d) ∧ (a₂ : Site d) ≠ (hub : Site d) ∧ (a₃ : Site d) ≠ (hub : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₂ : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₃ : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₂ : Site d) (a₃ : Site d) := by
-- proof
  apply StatMech.Walls.bft_count_hyp_of_fineTrif ω h hmem

/--
[bft_datum_sep_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_datum_sep_free_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site 2))}
  {S : Finset (Site 2)}
  {y : Site 2}
-- given
  (ιU : Site 2 → {v // v ∈ S})
  (hιU : ∀ y, ((ιU y : {v // v ∈ S}) : Site 2) = y)
  (hy : bft_FineTrif ω y)
  (hmem : ∀ a₁ a₂ a₃ : Site 2, ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable a₁ a₂ → ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable a₁ a₃ → ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable a₂ a₃ → a₁ ∈ S ∧ a₂ ∈ S ∧ a₃ ∈ S) :
-- imply
  ∃ v₁ v₂ v₃ : {v // v ∈ S}, v₁ ≠ ιU y ∧ v₂ ≠ ιU y ∧ v₃ ≠ ιU y ∧ ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable v₁ v₂ ∧ ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable v₁ v₃ ∧ ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable v₂ v₃ := by
-- proof
  apply StatMech.Walls.bft_datum_sep_free ω S ιU hιU hy hmem

/--
[bft_bk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_bk_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bft_bk p hp1 hp0 hdata

/--
[bft_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bftfinetrif.lean)
-/
@[path]
private lemma bft_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (x : Site d), bc67_contractedLattice ω 0 x = bkg_deleteVertex (openSubgraph d ω) x) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d)) {T : SimpleGraph {v // v ∈ S}} [_i : DecidableRel T.Adj], T ≤ bfct_restrict (openSubgraph d ω) S → T.IsTree → ∀ {ι : Type} [Fintype ι] (f : ι → {v // v ∈ S}), Function.Injective f → (∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, (a₁ : Site d) ≠ (f i : Site d) ∧ (a₂ : Site d) ≠ (f i : Site d) ∧ (a₃ : Site d) ≠ (f i : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₂ : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₃ : Site d) ∧ ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₂ : Site d) (a₃ : Site d)) → ∀ (B : Finset {v // v ∈ S}), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧ (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p → (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) → bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
-- proof
  apply StatMech.Walls.bft_status


-- created on 2026-10-23
