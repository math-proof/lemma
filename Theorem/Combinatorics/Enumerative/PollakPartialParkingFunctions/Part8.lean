/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PollakPartialParkingFunctions.lean -/

import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.PollakPartialParkingFunctions.Part7


namespace MetaMathlibExt.PollakPartialParking

theorem linTake_eq (s t : ℕ) (f : Fin s → Fin t) (n : ℕ) (h : n < s)
    (occ : { occ : Finset (Fin t) // occ.card ≤ n })
    (hm : linOccAux s t f n = some occ) :
    linTake s t f n h = linFirstFree t occ.val (f ⟨n, h⟩).val := by
  unfold linTake
  rw [hm]

/-- Success propagates backward: if step `n+1` succeeded, so did `n`. -/
theorem linOccAux_some_of_succ (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (h : (linOccAux s t f (n + 1)).isSome) : (linOccAux s t f n).isSome := by
  match hm : linOccAux s t f n with
  | none =>
    rw [linOccAux_succ_failed s t f n hm] at h
    simp at h
  | some _ => exact Option.isSome_some

theorem linOccAux_none_of_le (s t : ℕ) (f : Fin s → Fin t) (m k : ℕ)
    (hle : m ≤ k) (hm : linOccAux s t f m = none) :
    linOccAux s t f k = none :=
  Nat.le_induction (P := fun n _ => linOccAux s t f n = none) hm
    (fun n _ ih => linOccAux_succ_failed s t f n ih) k hle

theorem linOccAux_some_of_le (s t : ℕ) (f : Fin s → Fin t) (m : ℕ)
    (hle : m ≤ s) (hsucc : LinSuccess s t f) : (linOccAux s t f m).isSome := by
  unfold LinSuccess at hsucc
  match hm : linOccAux s t f m with
  | none =>
    rw [linOccAux_none_of_le s t f m s hle hm] at hsucc
    simp at hsucc
  | some _ => exact Option.isSome_some

theorem linOccAux_eq_some_of_isSome (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (h : (linOccAux s t f n).isSome) :
    ∃ occ, linOccAux s t f n = some occ :=
  Option.isSome_iff_exists.mp h

theorem linOcc_val_subset_step (s t : ℕ) (f : Fin s → Fin t) (n : ℕ)
    (hns : n < s)
    (oa : { occ : Finset (Fin t) // occ.card ≤ n })
    (oa' : { occ : Finset (Fin t) // occ.card ≤ n + 1 })
    (ha : linOccAux s t f n = some oa)
    (ha' : linOccAux s t f (n + 1) = some oa') :
    oa.val ⊆ oa'.val := by
  match hff : linFirstFree t oa.val (f ⟨n, hns⟩).val with
  | none =>
    rw [linOccAux_succ_none_take s t f n oa ha hns hff] at ha'
    simp at ha'
  | some x =>
    rw [linOccAux_succ_some s t f n oa ha hns x hff] at ha'
    have heq : oa'.val = insert x oa.val :=
      (congrArg Subtype.val (Option.some_inj.mp ha')).symm
    rw [heq]
    exact Finset.subset_insert x oa.val

theorem linOcc_val_subset (s t : ℕ) (f : Fin s → Fin t) (a b : ℕ)
    (hab : a ≤ b) (hbs : b ≤ s) (_hsucc : LinSuccess s t f)
    (oa : { occ : Finset (Fin t) // occ.card ≤ a })
    (ob : { occ : Finset (Fin t) // occ.card ≤ b })
    (ha : linOccAux s t f a = some oa) (hb : linOccAux s t f b = some ob) :
    oa.val ⊆ ob.val := by
  have key : ∀ n (hmn : a ≤ n), n ≤ b →
      ∀ (on : { occ : Finset (Fin t) // occ.card ≤ n }),
        linOccAux s t f n = some on → oa.val ⊆ on.val := by
    intro n
    exact Nat.le_induction
      (P := fun n _ => n ≤ b →
        ∀ (on : { occ : Finset (Fin t) // occ.card ≤ n }),
          linOccAux s t f n = some on → oa.val ⊆ on.val)
      (fun hnb on hon => by
        have heq : oa = on := Option.some_inj.mp (ha.symm.trans hon)
        rw [heq])
      (fun n hmn ih hnb on' hon' => by
        have hns : n < s := by omega
        have hs1 : (linOccAux s t f (n + 1)).isSome := hon'.symm ▸ Option.isSome_some
        have hs0 := linOccAux_some_of_succ s t f n hs1
        obtain ⟨on, hon⟩ := linOccAux_eq_some_of_isSome s t f n hs0
        exact Finset.Subset.trans (ih (by omega) on hon)
          (linOcc_val_subset_step s t f n hns on on' hon hon'))
      n
  exact key b hab (le_refl b) ob hb

theorem linTake_some_of_success (s t : ℕ) (f : Fin s → Fin t)
    (hsucc : LinSuccess s t f) (j : ℕ) (hj : j < s) :
    ∃ x, linTake s t f j hj = some x := by
  have h1 := linOccAux_some_of_le s t f (j + 1) (by omega) hsucc
  have h0 := linOccAux_some_of_le s t f j (by omega) hsucc
  obtain ⟨occ, hocc⟩ := linOccAux_eq_some_of_isSome s t f j h0
  match hffm : linFirstFree t occ.val (f ⟨j, hj⟩).val with
  | none =>
    obtain ⟨occ', hocc'⟩ := linOccAux_eq_some_of_isSome s t f (j + 1) h1
    rw [linOccAux_succ_none_take s t f j occ hocc hj hffm] at hocc'
    simp at hocc'
  | some x => exact ⟨x, by rw [linTake_eq s t f j hj occ hocc, hffm]⟩

end MetaMathlibExt.PollakPartialParking
