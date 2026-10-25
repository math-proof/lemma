import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bfctfinitecount.Part4
open Set SimpleGraph Finset StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation StatMech.Walls


/--
[bfct_restrict_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_restrict_adj_eq
  {G : SimpleGraph V}
  {S : Finset V}
-- given
  (a b : {v // v ∈ S}) :
-- imply
  (bfct_restrict G S).Adj a b ↔ G.Adj (a : V) (b : V) := by
-- proof
  apply StatMech.Walls.bfct_restrict_adj G S a b

/--
[bfct_reach_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_reach_transport_eq
  {G : SimpleGraph V}
  {S : Finset V}
  {t a b : {v // v ∈ S}}
-- given
  (h : (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b) :
-- imply
  (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V) := by
-- proof
  apply StatMech.Walls.bfct_reach_transport h

/--
[bfct_cut_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_cut_transport_eq
  {G : SimpleGraph V}
  {S : Finset V}
  {t a b : {v // v ∈ S}}
-- given
  (h : ¬ (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V)) :
-- imply
  ¬ (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b := by
-- proof
  apply StatMech.Walls.bfct_cut_transport h

/--
[bfct_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_count_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {S : Finset V}
  {T : SimpleGraph {v // v ∈ S}}
  [DecidableRel T.Adj]
  [Fintype ι]
-- given
  (hTH : T ≤ bfct_restrict G S)
  (hT : T.IsTree)
  (f : ι → {v // v ∈ S})
  (hf : Function.Injective f)
  (hcut : ∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧ ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₂ : V) ∧ ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₃ : V) ∧ ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₂ : V) (a₃ : V))
  (B : Finset {v // v ∈ S})
  (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
-- imply
  Fintype.card ι ≤ B.card := by
-- proof
  apply StatMech.Walls.bfct_count G S hTH hT f hf hcut B hleaf

/--
[bfct_hub_cut_of_separation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_hub_cut_of_separation_eq
  {G : SimpleGraph V}
  {S : Finset V}
  {w₁ w₂ w₃ : V}
-- given
  (hub : {v // v ∈ S})
  (hw₁ : w₁ ∈ S)
  (hw₂ : w₂ ∈ S)
  (hw₃ : w₃ ∈ S)
  (hn₁ : w₁ ≠ (hub : V))
  (hn₂ : w₂ ≠ (hub : V))
  (hn₃ : w₃ ≠ (hub : V))
  (hs₁₂ : ¬ (bkg_deleteVertex G (hub : V)).Reachable w₁ w₂)
  (hs₁₃ : ¬ (bkg_deleteVertex G (hub : V)).Reachable w₁ w₃)
  (hs₂₃ : ¬ (bkg_deleteVertex G (hub : V)).Reachable w₂ w₃) :
-- imply
  ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ hub ∧ a₂ ≠ hub ∧ a₃ ≠ hub ∧ ¬ (bkg_deleteVertex G (hub : V)).Reachable (a₁ : V) (a₂ : V) ∧ ¬ (bkg_deleteVertex G (hub : V)).Reachable (a₁ : V) (a₃ : V) ∧ ¬ (bkg_deleteVertex G (hub : V)).Reachable (a₂ : V) (a₃ : V) := by
-- proof
  apply StatMech.Walls.bfct_hub_cut_of_separation hub hw₁ hw₂ hw₃ hn₁ hn₂ hn₃ hs₁₂ hs₁₃ hs₂₃

/--
[bfct_origin_feed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_origin_feed_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {L : ℕ}
  {S : Finset (Site 2)}
-- given
  (h : bao_AllOpenTrif ω L)
  (h0S : (0 : Site 2) ∈ S)
  (hmem : ∀ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 → w₂ ≠ 0 → w₃ ≠ 0 → w₁ ∈ S ∧ w₂ ∈ S ∧ w₃ ∈ S) :
-- imply
  ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ (⟨0, h0S⟩ : {v // v ∈ S}) ∧ a₂ ≠ ⟨0, h0S⟩ ∧ a₃ ≠ ⟨0, h0S⟩ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable (a₁ : Site 2) (a₂ : Site 2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable (a₁ : Site 2) (a₃ : Site 2) ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable (a₂ : Site 2) (a₃ : Site 2) := by
-- proof
  apply StatMech.Walls.bfct_origin_feed h h0S hmem

/--
[bfct_reach_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_reach_isolated_eq
  {H : SimpleGraph V}
  {u : V}
  {a : V}
-- given
  (hiso : ∀ z, ¬ H.Adj u z)
  (h : H.Reachable a u) :
-- imply
  a = u := by
-- proof
  apply StatMech.Walls.bfct_reach_isolated hiso h

/--
[bfct_star_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_star_cut_eq :
-- imply
  ¬ (bkg_deleteVertex bfct_star (0 : Fin 4)).Reachable 1 2 := by
-- proof
  apply StatMech.Walls.bfct_star_cut

/--
[bfct_transport_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_transport_witness_eq :
-- imply
  ¬ (bkg_deleteVertex (bfct_restrict bfct_star bfct_starS) (⟨0, by decide⟩ : {v // v ∈ bfct_starS})).Reachable (⟨1, by decide⟩ : {v // v ∈ bfct_starS}) (⟨2, by decide⟩ : {v // v ∈ bfct_starS}) := by
-- proof
  apply StatMech.Walls.bfct_transport_witness

/--
[bfct_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bfctfinitecount.lean)
-/
@[path]
private lemma bfct_status_eq :
-- imply
  (∀ {V : Type} {G : SimpleGraph V} {S : Finset V} {t a b : {v // v ∈ S}}, ¬ (bkg_deleteVertex G (t : V)).Reachable (a : V) (b : V) → ¬ (bkg_deleteVertex (bfct_restrict G S) t).Reachable a b) ∧ (∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) {T : SimpleGraph {v // v ∈ S}} [_i : DecidableRel T.Adj], T ≤ bfct_restrict G S → T.IsTree → ∀ {ι : Type} [Fintype ι] (f : ι → {v // v ∈ S}), Function.Injective f → (∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S}, a₁ ≠ f i ∧ a₂ ≠ f i ∧ a₃ ≠ f i ∧ ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₂ : V) ∧ ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₁ : V) (a₃ : V) ∧ ¬ (bkg_deleteVertex G (f i : V)).Reachable (a₂ : V) (a₃ : V)) → ∀ (B : Finset {v // v ∈ S}), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧ (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L : ℕ), bao_AllOpenTrif ω L → ∃ w₁ w₂ w₃ : Site 2, w₁ ≠ 0 ∧ w₂ ≠ 0 ∧ w₃ ≠ 0 ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₂ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₁ w₃ ∧ ¬ (bkg_deleteVertex (bgf2_Gf ω L) 0).Reachable w₂ w₃) := by
-- proof
  apply StatMech.Walls.bfct_status


-- created on 2026-10-23
