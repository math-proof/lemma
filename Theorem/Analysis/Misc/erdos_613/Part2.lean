import Mathlib
import Def.Analysis.Misc.erdos_613.Part3
open Classical
open scoped BigOperators


namespace PikhurkoN5

open V

deriving instance Fintype for V

/-- $`|V| = 16`. Useful for quick cardinality arithmetic. -/
lemma card_V : Fintype.card V = 16 := by
  -- Reduce to the nested-sum cardinality and compute arithmetically.
  simpa using
    (Fintype.card_congr VEquiv).trans <|
      by
        -- `simp` turns cardinals of sums into sums of cardinals; `norm_num` does the rest.
        simp [Fintype.card_sum, Fintype.card_fin]

/-! # Degree computations

We compute the degree of each vertex *kind*. We’ll use your {attr}`@[simp]` adjacency
lemmas from Approach A:
- {name}`adj_apex_left`, {name}`adj_A1A1`, {name}`adj_A2A2`, {name}`adj_A1B1`, {name}`adj_A2B2`,
  and the corresponding “no edge” lemmas across blocks.
-/

/-- `deg(apex) = 15`. -/
lemma degree_apex : G.degree apex = 15 := by
  classical
  -- Neighbors of `apex` are exactly all vertices ≠ `apex`.
  have hN :
      G.neighborFinset apex = (Finset.univ.erase apex) := by
    ext v; constructor
    · intro hv
      have : G.Adj apex v := by simpa using hv
      have hvne : v ≠ apex := by simpa [adj_apex_left] using this
      simpa [Finset.mem_erase] using And.intro hvne (by simp : v ∈ (Finset.univ : Finset V))
    · intro hv
      have hvne : v ≠ apex := (Finset.mem_erase.mp hv).1
      have : G.Adj apex v := by simpa [adj_apex_left] using hvne
      simpa using this
  -- Count `univ.erase apex`.
  have : (G.neighborFinset apex).card = 15 := by
    -- `card (erase univ apex) = |V| - 1 = 16 - 1 = 15`
    have : (Finset.univ.erase apex).card = Fintype.card V - 1 := by
      have : apex ∈ (Finset.univ : Finset V) := by simp
      simp [Finset.card_erase_of_mem, this]
    simp [hN, card_V]
  -- `degree` is the cardinal of the neighbor finset.
  simp at this
  assumption

/-- `deg(A1 i) = 7` for each {name}`i`. -/
lemma degree_A1 (i : Fin 2) : G.degree (A1 i) = 7 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 1 + 5 + 0 + 0 + 1 := by
      congr
      . calc
        _ = Finset.card {j | j ≠ i} := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          grind
        _ = 1 := by
          fin_cases i <;> decide
      . calc
        _ = Finset.card (Finset.univ : Finset (Fin 5)) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 5 := by simp [Fintype.card_fin]
      . calc
        _ = Finset.card (∅ : Finset (Fin 3)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
          aesop
        _ = 0 := by simp
      . calc
        _ = Finset.card (∅: Finset (Fin 5)) := by
          congr; ext; simp [-iff_false]
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 0 := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num

/-- $`deg(B1 j) = 3` for each $`j`. (Two {name}`A1`s + apex.) -/
lemma degree_B1 (j : Fin 5) : G.degree (B1 j) = 3 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 2 + 0 + 0 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 2)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num

/-- $`deg(A2 i) = 8` for each $`i`. (Two inside {name}`A2` + five in {name}`B2` + apex.) -/
lemma degree_A2 (i : Fin 3) : G.degree (A2 i) = 8 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 2 + 5 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      . calc
          _ = Finset.card {j | j ≠ i} := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
            grind
          _ = _ := by
            convert Finset.card_erase_of_mem (show i ∈ Finset.univ by simp)
            · ext x; simp [Finset.mem_erase]
            · simp [Fintype.card_fin]
      . calc
          _ = Finset.card (Finset.univ: Finset (Fin 5)) := by
            congr; ext; simp
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv]
        _ = 1 := by simp
    _ = _ := by norm_num

/-- $`deg(B2 j) = 4` for each $`j`. (Three {name}`A2`s + apex.) -/
lemma degree_B2 (j : Fin 5) : G.degree (B2 j) = 4 := by
  rw [←G.card_neighborFinset_eq_degree, ←Finset.card_image_of_injective _ VEquiv.injective]
  simp_rw [←Finset.card_toLeft_add_card_toRight]
  calc
    _ = 0 + 0 + 3 + 0 + 1 := by
      congr
      . calc
          _ = Finset.card (∅ : Finset (Fin 2)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (Finset.univ : Finset (Fin 3)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      . calc
          _ = Finset.card (∅: Finset (Fin 5)) := by
            congr; ext; simp [-iff_false]
            simp_rw [←Equiv.eq_symm_apply VEquiv]
            simp [VEquiv, G, GAdj]
          _ = _ := by simp
      calc
        _ = Finset.card (Finset.univ : Finset Unit) := by
          congr; ext; simp
          simp_rw [←Equiv.eq_symm_apply VEquiv]
          simp [VEquiv, G, GAdj]
        _ = 1 := by simp
    _ = _ := by norm_num

/-!
# Edge count via the handshaking lemma
We now sum the degrees and divide by 2.
-/
theorem edge_count_44 : G.edgeSet.ncard = 44 := by
  classical
  -- Handshaking lemma on edge *set* cardinality.
  -- In current mathlib this comes as:
  --   `G.sum_degrees_eq_twice_card_edgeSet : (∑ v, G.degree v) = 2 * G.edgeSet.ncard`.
  have hand := G.sum_degrees_eq_twice_card_edges
  rw [←SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [←Equiv.sum_comp VEquiv.symm _] at hand
  simp_rw [Fintype.sum_sum_type] at hand
  have : ∀ i, G.degree (VEquiv.symm (.inl (.inl (.inl (.inl i))))) = G.degree (A1 i) := fun _ => rfl
  have : ∀ j, G.degree (VEquiv.symm (.inl (.inl (.inl (.inr j))))) = G.degree (B1 j) := fun _ => rfl
  have : ∀ i, G.degree (VEquiv.symm (.inl (.inl (.inr i)))) = G.degree (A2 i) := fun _ => rfl
  have : ∀ j, G.degree (VEquiv.symm (.inl (.inr j))) = G.degree (B2 j) := fun _ => rfl
  have : ∀ u, G.degree (VEquiv.symm (.inr u)) = G.degree apex := fun _ => rfl
  simp_all [degree_A1, degree_B1, degree_A2, degree_B2, degree_apex]; omega

end PikhurkoN5

-- 4. Show red neighbors of apex are ≥ 11 if no blue K_{1,5}

namespace PikhurkoN5

open V

/-! # Small utilities -/

/- Pick a `k`-subset of a finset `s` when `k ≤ s.card`. -/

namespace Finset

variable {α : Type*}

lemma exists_subset_card_eq (s : Finset α) {k : ℕ} (hk : k ≤ s.card) :
  ∃ t ⊆ s, t.card = k := by
  exact Finset.le_card_iff_exists_subset_card.mp hk

end Finset

/-- In {lean}`Fin 2`, saying “equals {lean (type := "Fin 2")}`1`” is the same as “not equal to {lean (type := "Fin 2")}`0`”. -/
lemma fin2_eq_one_iff_ne_zero (a : Fin 2) : (a = 1) ↔ a ≠ 0 := by
  fin_cases a <;> simp

end PikhurkoN5
