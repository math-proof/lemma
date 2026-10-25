/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/ParkingFunction.lean -/


import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
open MetaMathlibExt


example (n : ℕ) (f : Fin n → Fin n) :
    IsParkingFunction n f ↔
      ∀ k : Fin n,
        k.val + 1 ≤ (Finset.univ.filter (fun i : Fin n ↦ f i ≤ k)).card :=
  isParkingFunction_iff_card_filter_le n f

example : IsParkingFunction 0 (fun i => i.elim0) := by decide

example : IsParkingFunction 2 (fun i => i) := by decide

example : ¬IsParkingFunction 2 (fun _ => (1 : Fin 2)) := by decide

