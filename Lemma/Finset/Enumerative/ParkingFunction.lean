import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.Combinatorics.Enumerative.ParkingFunction
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isParkingFunction_iff_card_filter_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ParkingFunction.lean)
-/
@[path]
lemma isParkingFunction_iff_card_filter_le
  {n : ℕ}
  {f : Fin n → Fin n} :
-- imply
  IsParkingFunction n f ↔
    ∀ k : Fin n,
    k.val + 1 ≤ (Finset.univ.filter (fun i : Fin n ↦ f i ≤ k)).card := by
-- proof
  constructor
  · intro hf k
    unfold IsParkingFunction IsPartialParkingFunction at hf
    by_cases hk : k.val + 1 < n
    · let l : Fin n := ⟨k.val + 1, hk⟩
      have hl := hf l
      have hpart :
        (Finset.univ.filter (fun i : Fin n ↦ f i ≤ k)).card +
          (Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ k)).card = n := by
        simpa using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n ↦ f i ≤ k))
      have hfilter :
        Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ k) =
          Finset.univ.filter (fun i : Fin n ↦ l ≤ f i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (¬(f i).val ≤ k.val) ↔ k.val + 1 ≤ (f i).val
        omega
      rw [hfilter] at hpart
      change
        (Finset.univ.filter (fun i : Fin n ↦ l ≤ f i)).card ≤ n - (k.val + 1) at hl
      omega
    · have hfilter :
      Finset.univ.filter (fun i : Fin n ↦ f i ≤ k) = Finset.univ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro
        trivial
      · intro
        change (f i).val ≤ k.val
        omega
      rw [hfilter, Finset.card_univ, Fintype.card_fin]
      omega
  · intro hf
    unfold IsParkingFunction IsPartialParkingFunction
    intro k
    by_cases hk : k.val = 0
    · calc
      (Finset.univ.filter (fun i : Fin n ↦ k ≤ f i)).card ≤
        (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
      _ = n := Fintype.card_fin n
      _ = n - k.val := by omega
    · let p : Fin n := ⟨k.val - 1, by omega⟩
      have hp := hf p
      have hpart :
        (Finset.univ.filter (fun i : Fin n ↦ f i ≤ p)).card +
          (Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ p)).card = n := by
        simpa using
          (Finset.card_filter_add_card_filter_not
            (s := (Finset.univ : Finset (Fin n))) (fun i : Fin n ↦ f i ≤ p))
      have hfilter :
        Finset.univ.filter (fun i : Fin n ↦ ¬f i ≤ p) =
          Finset.univ.filter (fun i : Fin n ↦ k ≤ f i) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        change (¬(f i).val ≤ k.val - 1) ↔ k.val ≤ (f i).val
        omega
      rw [hfilter] at hpart
      change
        k.val - 1 + 1 ≤
          (Finset.univ.filter (fun i : Fin n ↦ f i ≤ p)).card at hp
      omega

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
