/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part4


namespace MetaMathlibExt.PollakPartialParking

theorem card_parkEmpty (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t) :
    (parkEmpty s t g hst).card = t + 1 - s := by
  unfold parkEmpty
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, ZMod.card,
    card_parkOcc_self s t g hst]

theorem firstFree_translate (t : ℕ) (occ : Finset (ZMod (t + 1)))
    (a c : ZMod (t + 1)) (h : occ.card < t + 1)
    (h' : (Finset.image (fun x => x + c) occ).card < t + 1) :
    firstFree t (Finset.image (fun x => x + c) occ) (a + c) h' =
      firstFree t occ a h + c := by
  have hPQ : ∀ j : ℕ,
      ((a + c) + (((j : ℕ)) : ZMod (t + 1))
        ∉ Finset.image (fun x => x + c) occ) ↔
      (a + (((j : ℕ)) : ZMod (t + 1)) ∉ occ) := by
    intro j
    have hshift : (a + c) + (((j : ℕ)) : ZMod (t + 1))
        = (a + (((j : ℕ)) : ZMod (t + 1))) + c := by ring
    rw [hshift]
    constructor
    · intro hcon hmem
      apply hcon
      rw [Finset.mem_image]
      exact ⟨_, hmem, rfl⟩
    · intro hcon hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨x, hxmem, hxeq⟩ := hmem
      apply hcon
      have hx : x = a + (((j : ℕ)) : ZMod (t + 1)) := add_right_cancel hxeq
      rwa [hx] at hxmem
  have HP := ray_free_exists t occ a h
  have HQ := ray_free_exists t (Finset.image (fun x => x + c) occ) (a + c) h'
  have h1 : Nat.find HP ≤ Nat.find HQ :=
    Nat.find_min' HP ((hPQ _).mp (Nat.find_spec HQ))
  have h2 : Nat.find HQ ≤ Nat.find HP :=
    Nat.find_min' HQ ((hPQ _).mpr (Nat.find_spec HP))
  have hfind : Nat.find HP = Nat.find HQ := le_antisymm h1 h2
  unfold firstFree
  rw [hfind]
  ring

theorem parkOcc_translate (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (c : ZMod (t + 1)) (n : ℕ) :
    parkOcc s t (fun i => g i + c) hst n =
      Finset.image (fun x => x + c) (parkOcc s t g hst n) := by
  induction n with
  | zero =>
    simp only [parkOcc, parkOccAux, Finset.image_empty]
  | succ n ih =>
    by_cases h : n < s
    · have hassign : parkAssign s t (fun i => g i + c) hst n h =
          parkAssign s t g hst n h + c := by
        unfold parkAssign
        simp only [ih]
        exact firstFree_translate t (parkOcc s t g hst n) (g ⟨n, h⟩) c _ _
      rw [parkOcc_succ_of_lt s t (fun i => g i + c) hst n h,
        parkOcc_succ_of_lt s t g hst n h, Finset.image_insert, ih, hassign]
    · rw [parkOcc_succ_of_ge s t (fun i => g i + c) hst n h,
        parkOcc_succ_of_ge s t g hst n h, ih]

theorem parkEmpty_translate (s t : ℕ) (g : Fin s → ZMod (t + 1)) (hst : s ≤ t)
    (c : ZMod (t + 1)) :
    parkEmpty s t (fun i => g i + c) hst =
      Finset.image (fun x => x + c) (parkEmpty s t g hst) := by
  have hinj : Function.Injective (fun x : ZMod (t + 1) => x + c) :=
    fun a b hab => add_right_cancel hab
  have hsurj : Function.Surjective (fun x : ZMod (t + 1) => x + c) :=
    fun y => ⟨y - c, by ring⟩
  unfold parkEmpty
  rw [parkOcc_translate s t g hst c s]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hsurj x
    subst hy
    rw [Finset.mem_image]
    refine ⟨y, ?_, rfl⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hyocc
    exact hx (Finset.mem_image_of_mem _ hyocc)
  · intro hx
    rw [Finset.mem_image] at hx
    obtain ⟨y, hyocc, hyeq⟩ := hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hyocc
    intro hximg
    rw [Finset.mem_image] at hximg
    obtain ⟨z, hzocc, hzeq⟩ := hximg
    have hyz : y = z := hinj (hyeq.trans hzeq.symm)
    rw [← hyz] at hzocc
    exact hyocc hzocc

end MetaMathlibExt.PollakPartialParking
