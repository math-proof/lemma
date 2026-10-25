/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution.Part6
open Asymptotics Filter Finset


namespace Green25

def repeatPartition25 {B : ℕ} (q : ℕ) (hB : 0 < B)
    (P : Finpartition (Icc 1 B)) : Finpartition (Icc 1 (q * B)) := by
  let block : Fin q → Finset ℕ := fun i => shift25 (i.1 * B) (Icc 1 B)
  let part : (i : Fin q) → Finpartition (block i) := fun i => shiftPartition25 (i.1 * B) P
  have hind : (Finset.univ : Finset (Fin q)).SupIndep block := by
    rw [Finset.supIndep_iff_pairwiseDisjoint]
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Finset.mem_coe, Finset.mem_univ,
      Function.onFun, id_eq, ne_eq, forall_const]
    intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [block, shift25, Finset.mem_image, Finset.mem_Icc] at hxi hxj
    obtain ⟨u, ⟨hu1, huB⟩, hux⟩ := hxi
    obtain ⟨v, ⟨hv1, hvB⟩, hvx⟩ := hxj
    have heq : i.1 = j.1 := by nlinarith
    exact hij (Fin.ext heq)
  have hsup : (Finset.univ : Finset (Fin q)).sup block = Icc 1 (q * B) := by
    ext x
    simp only [Finset.mem_sup, Finset.mem_univ, true_and, block, shift25,
      Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨i, y, ⟨hy1, hyB⟩, rfl⟩
      constructor
      · omega
      · have hi := i.isLt
        nlinarith
    · rintro ⟨hx1, hxq⟩
      let i : Fin q := ⟨(x - 1) / B, by
        apply (Nat.div_lt_iff_lt_mul hB).2
        omega⟩
      let y := (x - 1) % B + 1
      refine ⟨i, y, ?_, ?_⟩
      · constructor
        · omega
        · have hm := Nat.mod_lt (x - 1) hB
          omega
      · dsimp [i, y]
        calc
          (x - 1) / B * B + ((x - 1) % B + 1) =
              (x - 1) % B + B * ((x - 1) / B) + 1 := by ac_rfl
          _ = x := by
            calc
              (x - 1) % B + B * ((x - 1) / B) + 1 = (x - 1) + 1 :=
                congrArg (· + 1) (Nat.mod_add_div (x - 1) B)
              _ = x := Nat.sub_add_cancel hx1
  exact {
    parts := (Finset.univ : Finset (Fin q)).biUnion fun i => (part i).parts
    supIndep := Finset.SupIndep.biUnion (by
      change (Finset.univ : Finset (Fin q)).SupIndep
        (fun i => (part i).parts.sup id)
      have heq : (fun i => (part i).parts.sup id) = block := by
        funext i
        exact (part i).sup_parts
      rw [heq]
      exact hind)
      (fun i _ => (part i).supIndep)
    sup_parts := by
      rw [Finset.sup_biUnion]
      calc
        (Finset.univ : Finset (Fin q)).sup (fun i => (part i).parts.sup id) =
            (Finset.univ : Finset (Fin q)).sup block := by
              apply Finset.sup_congr rfl
              intro i _
              exact (part i).sup_parts
        _ = Icc 1 (q * B) := hsup
    bot_notMem := by
      rw [Finset.mem_biUnion]
      push_neg
      exact fun i _ => (part i).bot_notMem }

end Green25
