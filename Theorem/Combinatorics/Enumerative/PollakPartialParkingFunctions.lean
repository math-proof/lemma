/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring


namespace MetaMathlibExt.PollakPartialParking

/-- On the circle `ZMod (t+1)`, the clockwise ray from `a` always hits a spot
outside `occ` when `occ` is not full. -/
theorem ray_free_exists (t : ℕ) (occ : Finset (ZMod (t + 1))) (a : ZMod (t + 1))
    (h : occ.card < t + 1) : ∃ j : ℕ, a + ((j : ℕ) : ZMod (t + 1)) ∉ occ := by
  have hinj : Function.Injective
      (fun j : Fin (t + 1) => a + (((j.val : ℕ)) : ZMod (t + 1))) := by
    intro j1 j2 h12
    have hcast : (((j1.val : ℕ)) : ZMod (t + 1)) = (((j2.val : ℕ)) : ZMod (t + 1)) :=
      add_left_cancel h12
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    have heq := hcast.eq_of_lt_of_lt j1.isLt j2.isLt
    exact Fin.ext heq
  have hcard : (Finset.univ.image
      (fun j : Fin (t + 1) => a + (((j.val : ℕ)) : ZMod (t + 1)))).card = t + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hnot : ¬ (Finset.univ.image
      (fun j : Fin (t + 1) => a + (((j.val : ℕ)) : ZMod (t + 1)))) ⊆ occ := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  rw [Finset.not_subset] at hnot
  obtain ⟨x, hximg, hxnocc⟩ := hnot
  rw [Finset.mem_image] at hximg
  obtain ⟨j, _, rfl⟩ := hximg
  exact ⟨j.val, hxnocc⟩

end MetaMathlibExt.PollakPartialParking
