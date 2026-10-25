/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.W4PathDominoTilings.Part5
open SimpleGraph


section

namespace MetaMathlibExt

noncomputable def horizPairingOf (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) (j : ℕ) (hj : j < m) :
    HorizPairing (leftoverSet m M hM j) := by
  refine ⟨horizFunNat m M hM j, ?_, ?_⟩
  · intro a hmem
    have hnot : a ∉ (belowSet m M hM j ∪ aboveSet m M hM j) :=
      (leftover_mem m M hM j a).mp hmem
    have hsame := not_mem_union_same_layer m M hM j hj a hnot
    have hfa : horizFunNat m M hM j a = (partner m M hM (a, ⟨j, hj⟩)).1 :=
      horizFunNat_of_mem m M hM j hj a hmem
    have hW : W4.Adj a (partner m M hM (a, ⟨j, hj⟩)).1 :=
      partner_same_layer_horiz m M hM a ⟨j, hj⟩ hsame
    have hW' : W4.Adj a (horizFunNat m M hM j a) := by rw [hfa]; exact hW
    have hne : a ≠ horizFunNat m M hM j a := ((W4_adj a _).mp hW').1
    have hne' : horizFunNat m M hM j a ≠ a := Ne.symm hne
    have hpeq : partner m M hM (a, ⟨j, hj⟩) =
        (horizFunNat m M hM j a, ⟨j, hj⟩) :=
      Prod.ext hfa.symm hsame
    have hsym : partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩) = (a, ⟨j, hj⟩) := by
      have hps := partner_symm m M hM (a, ⟨j, hj⟩)
      rw [hpeq] at hps
      exact hps
    have hbmem : horizFunNat m M hM j a ∈ leftoverSet m M hM j := by
      rw [leftover_mem]
      intro hcon
      rw [Finset.mem_union] at hcon
      rcases hcon with hb | ha
      · by_cases hj0 : j = 0
        · subst hj0
          unfold belowSet at hb
          exact (Finset.notMem_empty _) hb
        · obtain ⟨k, hk, heq⟩ := below_mem_down m M hM j hj hj0 _ hb
          have h1 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = k :=
            congrArg Prod.snd heq
          have h2 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ :=
            congrArg Prod.snd hsym
          have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans h2
          have hval : k.val = j := congrArg Fin.val hkk
          omega
      · obtain ⟨k, hk, heq⟩ := above_mem_up m M hM j hj _ ha
        have h1 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = k :=
          congrArg Prod.snd heq
        have h2 : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).2 = ⟨j, hj⟩ :=
          congrArg Prod.snd hsym
        have hkk : k = (⟨j, hj⟩ : Fin m) := h1.symm.trans h2
        have hval : k.val = j := congrArg Fin.val hkk
        omega
    have hfb : horizFunNat m M hM j (horizFunNat m M hM j a) = a := by
      have hfb' : horizFunNat m M hM j (horizFunNat m M hM j a) =
          (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).1 :=
        horizFunNat_of_mem m M hM j hj _ hbmem
      rw [hfb']
      have : (partner m M hM (horizFunNat m M hM j a, ⟨j, hj⟩)).1 = a :=
        congrArg Prod.fst hsym
      exact this
    exact ⟨hbmem, hfb, hne', hW'⟩
  · intro a hmem
    exact horizFunNat_of_not_mem m M hM j hj a hmem

-- Top holes for the prefix of length `k`: empty at 0, else the boundary below.
noncomputable def topHoles (m : ℕ) (M : (W4 □ pathGraph m).Subgraph)
    (hM : M.IsPerfectMatching) : ℕ → Finset (Fin 4)
  | 0 => ∅
  | (k + 1) => vertSet m M hM k

end MetaMathlibExt
end
