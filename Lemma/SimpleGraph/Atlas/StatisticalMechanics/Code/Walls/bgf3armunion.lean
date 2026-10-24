import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.bgf3armunion
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bgf3_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_adj_iff_eq
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  {u v : V} :
-- imply
  (bgf3_G ray len).Adj u v ↔ (∃ (α : Arm) (k : ℕ), k < len α ∧ s(u, v) = s(ray α k, ray α (k + 1))) ∧ u ≠ v := by
-- proof
  apply StatMech.Walls.bgf3_adj_iff ray len u v

/--
[bgf3_adj_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_adj_step_eq
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  {α : Arm}
  {k : ℕ}
-- given
  (hk : k < len α)
  (hne : ray α k ≠ ray α (k + 1)) :
-- imply
  (bgf3_G ray len).Adj (ray α k) (ray α (k + 1)) := by
-- proof
  apply StatMech.Walls.bgf3_adj_step ray len α hk hne

/--
[bgf3_le_tree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_le_tree_eq
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  {T : SimpleGraph V}
-- given
  (hadjT : ∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) :
-- imply
  bgf3_G ray len ≤ T := by
-- proof
  apply StatMech.Walls.bgf3_le_tree ray len T hadjT

/--
[bgf3_acyclic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_acyclic_eq
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  {T : SimpleGraph V}
-- given
  (hT : T.IsTree)
  (hadjT : ∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) :
-- imply
  (bgf3_G ray len).IsAcyclic := by
-- proof
  apply StatMech.Walls.bgf3_acyclic ray len hT hadjT

/--
[bgf3_two_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_two_le_degree_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v a b : V}
-- given
  (hab : a ≠ b)
  (ha : G.Adj v a)
  (hb : G.Adj v b) :
-- imply
  2 ≤ G.degree v := by
-- proof
  apply StatMech.Walls.bgf3_two_le_degree G hab ha hb

/--
[bgf3_three_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_three_le_degree_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v a b c : V}
-- given
  (hab : a ≠ b)
  (hac : a ≠ c)
  (hbc : b ≠ c)
  (ha : G.Adj v a)
  (hb : G.Adj v b)
  (hc : G.Adj v c) :
-- imply
  3 ≤ G.degree v := by
-- proof
  apply StatMech.Walls.bgf3_three_le_degree G hab hac hbc ha hb hc

/--
[bgf3_interior_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_interior_two_le_eq
  [Fintype V]
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  [DecidableRel (bgf3_G ray len).Adj]
  {α : Arm}
  {j : ℕ}
-- given
  (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
  (hj0 : 0 < j)
  (hjlen : j < len α) :
-- imply
  2 ≤ (bgf3_G ray len).degree (ray α j) := by
-- proof
  apply StatMech.Walls.bgf3_interior_two_le ray len hinj α hj0 hjlen

/--
[bgf3_deg3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_deg3_eq
  [Fintype V]
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  [DecidableRel (bgf3_G ray len).Adj]
  {f : ι → V}
  {arm3 : ι → Fin 3 → Arm}
  {i : ι}
-- given
  (hlen : ∀ α, 1 ≤ len α)
  (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
  (harm3start : ∀ i j, ray (arm3 i j) 0 = f i)
  (harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1) :
-- imply
  3 ≤ (bgf3_G ray len).degree (f i) := by
-- proof
  apply StatMech.Walls.bgf3_deg3 ray len hlen hinj f arm3 harm3start harm3dist i

/--
[bgf3_one_le_degree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_one_le_degree_eq
  [Fintype V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {v a : V}
-- given
  (ha : G.Adj v a) :
-- imply
  1 ≤ G.degree v := by
-- proof
  apply StatMech.Walls.bgf3_one_le_degree G ha

/--
[bgf3_min_deg1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_min_deg1_eq
  [Fintype V]
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  [DecidableRel (bgf3_G ray len).Adj]
  {v : V}
-- given
  (hlen : ∀ α, 1 ≤ len α)
  (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
  (hcover : ∀ v, ∃ (α : Arm) (j : ℕ), j ≤ len α ∧ ray α j = v) :
-- imply
  1 ≤ (bgf3_G ray len).degree v := by
-- proof
  apply StatMech.Walls.bgf3_min_deg1 ray len hlen hinj hcover v

/--
[bgf3_leaves_on_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_leaves_on_boundary_eq
  [Fintype V]
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  [DecidableRel (bgf3_G ray len).Adj]
  {B : Finset V}
  {f : ι → V}
  {arm3 : ι → Fin 3 → Arm}
  {v : V}
-- given
  (hlen : ∀ α, 1 ≤ len α)
  (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
  (htip : ∀ α, ray α (len α) ∈ B)
  (harm3start : ∀ i j, ray (arm3 i j) 0 = f i)
  (harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1)
  (hhub : ∀ α, ∃ i, ray α 0 = f i)
  (hdeg : (bgf3_G ray len).degree v = 1) :
-- imply
  v ∈ B := by
-- proof
  apply StatMech.Walls.bgf3_leaves_on_boundary ray len hlen hinj htip f arm3 harm3start harm3dist hhub hdeg

/--
[bgf3_count](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_count_eq
  [Fintype V]
  [Nonempty V]
  {ray : Arm → ℕ → V}
  {len : Arm → ℕ}
  [DecidableRel (bgf3_G ray len).Adj]
  {T : SimpleGraph V}
  {B : Finset V}
  [Fintype ι]
  {f : ι → V}
  {arm3 : ι → Fin 3 → Arm}
-- given
  (hT : T.IsTree)
  (hadjT : ∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1)))
  (hlen : ∀ α, 1 ≤ len α)
  (hinj : ∀ α, Set.InjOn (ray α) {n | n ≤ len α})
  (hcover : ∀ v, ∃ (α : Arm) (j : ℕ), j ≤ len α ∧ ray α j = v)
  (htip : ∀ α, ray α (len α) ∈ B)
  (hf : Function.Injective f)
  (harm3start : ∀ i j, ray (arm3 i j) 0 = f i)
  (harm3dist : ∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1)
  (hhub : ∀ α, ∃ i, ray α 0 = f i) :
-- imply
  Fintype.card ι ≤ B.card := by
-- proof
  apply StatMech.Walls.bgf3_count ray len hT hadjT hlen hinj hcover htip f hf arm3 harm3start harm3dist hhub

/--
[bgf3_star_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_star_witness_eq :
-- imply
  Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card := by
-- proof
  apply StatMech.Walls.bgf3_star_witness

/--
[bgf3_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bgf3armunion.lean)
-/
@[path]
private lemma bgf3_status_eq :
-- imply
  (∀ {V : Type} {Arm : Type} (ray : Arm → ℕ → V) (len : Arm → ℕ) {T : SimpleGraph V}, T.IsTree → (∀ α, ∀ k < len α, T.Adj (ray α k) (ray α (k + 1))) → (bgf3_G ray len).IsAcyclic) ∧ (∀ {V : Type} [Fintype V] {Arm : Type} (ray : Arm → ℕ → V) (len : Arm → ℕ) [DecidableRel (bgf3_G ray len).Adj], (∀ α, 1 ≤ len α) → (∀ α, Set.InjOn (ray α) {n | n ≤ len α}) → ∀ {B : Finset V}, (∀ α, ray α (len α) ∈ B) → ∀ {ι : Type} (f : ι → V) (arm3 : ι → Fin 3 → Arm), (∀ i j, ray (arm3 i j) 0 = f i) → (∀ i (j j' : Fin 3), j ≠ j' → ray (arm3 i j) 1 ≠ ray (arm3 i j') 1) → (∀ α, ∃ i, ray α 0 = f i) → ∀ {v : V}, (bgf3_G ray len).degree v = 1 → v ∈ B) ∧ (Fintype.card (Fin 1) ≤ ({1, 2, 3} : Finset (Fin 4)).card) := by
-- proof
  apply StatMech.Walls.bgf3_status


-- created on 2026-10-23
