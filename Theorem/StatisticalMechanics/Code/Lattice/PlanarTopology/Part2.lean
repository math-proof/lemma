/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Instance.StatisticalMechanics.Code.Lattice.PlanarTopology.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem neighborFinset_eq_candFinset (d : ℕ) (x : Site d) :
    (hypercubicLattice d).neighborFinset x = candFinset d x := by
  apply Finset.ext
  intro y
  rw [SimpleGraph.mem_neighborFinset]
  refine ⟨fun h => mem_candFinset_of_adj d x y h, ?_⟩
  intro hy
  rw [candFinset, Finset.mem_image] at hy
  obtain ⟨p, _, rfl⟩ := hy
  exact adj_candMap d x p


theorem card_candFinset (d : ℕ) (x : Site d) : (candFinset d x).card = 2 * d := by
  rw [candFinset, Finset.card_image_of_injective _ (candMap_injective d x),
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring


theorem degree_eq (d : ℕ) (x : Site d) : (hypercubicLattice d).degree x = 2 * d := by
  rw [SimpleGraph.degree, neighborFinset_eq_candFinset, card_candFinset]


theorem isRegularOfDegree (d : ℕ) :
    (hypercubicLattice d).IsRegularOfDegree (2 * d) := degree_eq d


theorem degree_le (d : ℕ) (x : Site d) : (hypercubicLattice d).degree x ≤ 2 * d :=
  (degree_eq d x).le


section Counting

variable {V : Type*} (G : SimpleGraph V) [DecidableEq V] [SimpleGraph.LocallyFinite G]


theorem card_finsetWalkLength_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v).card ≤ D ^ n := by
  induction n generalizing u with
  | zero =>
    rw [pow_zero, Finset.card_le_one]
    intro a ha b hb
    rw [SimpleGraph.mem_finsetWalkLength_iff] at ha hb
    have hav := SimpleGraph.Walk.eq_of_length_eq_zero ha
    subst hav
    rw [SimpleGraph.Walk.length_eq_zero_iff] at ha hb
    rw [ha.eq_nil, hb.eq_nil]
  | succ n ih =>
    rw [SimpleGraph.finsetWalkLength]
    calc (Finset.univ.biUnion (fun (w : G.neighborSet u) =>
            (G.finsetWalkLength n w v).map
              ⟨fun p => Walk.cons w.property p, fun _ _ h => by injection h with _ hp; exact hp⟩)).card
        ≤ ∑ w : G.neighborSet u,
            ((G.finsetWalkLength n (w : V) v).map
              ⟨fun p => Walk.cons w.property p, fun _ _ h => by injection h with _ hp; exact hp⟩).card :=
          Finset.card_biUnion_le
      _ = ∑ w : G.neighborSet u, (G.finsetWalkLength n (w : V) v).card := by
          apply Finset.sum_congr rfl
          intro w _
          rw [Finset.card_map]
      _ ≤ ∑ _w : G.neighborSet u, D ^ n := Finset.sum_le_sum (fun w _ => ih (w : V))
      _ = (Fintype.card (G.neighborSet u)) * D ^ n := by
          rw [Finset.sum_const, Finset.card_univ]; ring
      _ = G.degree u * D ^ n := by rw [← SimpleGraph.card_neighborSet_eq_degree]
      _ ≤ D * D ^ n := Nat.mul_le_mul_right _ (hD u)
      _ = D ^ (n + 1) := by rw [pow_succ]; ring


theorem card_finsetWalkLength_self_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (n : ℕ) (v : V) :
    (G.finsetWalkLength n v v).card ≤ D ^ n :=
  card_finsetWalkLength_le G hD n v v


theorem card_circuits_based_in_le {D : ℕ} (hD : ∀ v, G.degree v ≤ D) (B : Finset V) (n : ℕ) :
    (B.sigma (fun v => G.finsetWalkLength n v v)).card ≤ B.card * D ^ n := by
  rw [Finset.card_sigma]
  calc ∑ v ∈ B, (G.finsetWalkLength n v v).card
      ≤ ∑ _v ∈ B, D ^ n :=
        Finset.sum_le_sum (fun v _ => card_finsetWalkLength_le G hD n v v)
    _ = B.card * D ^ n := by rw [Finset.sum_const, smul_eq_mul]

end Counting


theorem card_finsetWalkLength_le_pow (d n : ℕ) (u v : Site d) :
    ((hypercubicLattice d).finsetWalkLength n u v).card ≤ (2 * d) ^ n :=
  card_finsetWalkLength_le (hypercubicLattice d) (degree_le d) n u v


theorem card_circuits_le_pow (d n : ℕ) (v : Site d) :
    ((hypercubicLattice d).finsetWalkLength n v v).card ≤ (2 * d) ^ n :=
  card_finsetWalkLength_le_pow d n v v


theorem card_circuits_based_in_le_pow (d : ℕ) (B : Finset (Site d)) (n : ℕ) :
    (B.sigma (fun v => (hypercubicLattice d).finsetWalkLength n v v)).card
      ≤ B.card * (2 * d) ^ n :=
  card_circuits_based_in_le (hypercubicLattice d) (degree_le d) B n


end Lattice
end StatMech
