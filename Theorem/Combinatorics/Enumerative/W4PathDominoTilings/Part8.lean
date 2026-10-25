/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/W4PathDominoTilings.lean -/

import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Data.Nat.Fib.Basic
import Def.NumberTheory.PellNumberSequence
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.W4PathDominoTilings.Part10
open SimpleGraph


section

namespace MetaMathlibExt

theorem tiling_props : ∀ (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling m S')
    (j : ℕ) (_hj : j < m),
    Disjoint (if j = 0 then ∅ else getS m S' t (j - 1)) (getS m S' t j) ∧
    HorizProps (getF m S' t j)
      (Finset.univ \ ((if j = 0 then ∅ else getS m S' t (j - 1)) ∪ getS m S' t j)) := by
  intro m
  induction m with
  | zero =>
    intro S' t j hj
    exact absurd hj (Nat.not_lt_zero j)
  | succ m ih =>
    intro S' t j _hj
    cases t with
    | mk S snd =>
      cases snd with
      | mk hd rest =>
        cases rest with
        | mk tm h =>
          by_cases hjm : j = m
          · rw [hjm]
            have hSe : getS (m + 1) S' ⟨S, hd, tm, h⟩ m = S' := by
              simp only [getS, ite_true]
            have hFe : getF (m + 1) S' ⟨S, hd, tm, h⟩ m = h.val := by
              simp only [getF, ite_true]
            have hbelow : (if m = 0 then ∅ else getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1)) = S := by
              by_cases hm0 : m = 0
              · subst hm0
                simp only [ite_true]
                have : S = ∅ := tm.down
                exact this.symm
              · have h1 : (if m = 0 then ∅ else getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1)) =
                    getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1) := by
                  simp only [ite_eq_right hm0]
                rw [h1]
                have hne : m - 1 ≠ m := by omega
                have h2 : getS (m + 1) S' ⟨S, hd, tm, h⟩ (m - 1) = getS m S tm (m - 1) := by
                  simp only [getS, ite_eq_right hne]
                rw [h2]
                cases m with
                | zero => exact absurd rfl hm0
                | succ m' =>
                  have hsub : m' + 1 - 1 = m' := rfl
                  rw [hsub]
                  have : getS (m' + 1) S tm m' = S := by
                    cases tm with
                    | mk _ _ =>
                      simp only [getS, ite_true]
                  exact this
            rw [hbelow, hSe, hFe]
            have hU : Finset.univ \ (S ∪ S') = Finset.univ \ (S ∪ S') := rfl
            refine ⟨?_, ?_⟩
            · have : Disjoint S S' := hd.down
              exact this
            · have hp := h.property
              exact hp
          · have hjm' : j < m := by omega
            have hSj : getS (m + 1) S' ⟨S, hd, tm, h⟩ j = getS m S tm j := by
              simp only [getS, ite_eq_right hjm]
            have hFj : getF (m + 1) S' ⟨S, hd, tm, h⟩ j = getF m S tm j := by
              simp only [getF, ite_eq_right hjm]
            have hSlow : (if j = 0 then ∅ else getS (m + 1) S' ⟨S, hd, tm, h⟩ (j - 1)) =
                (if j = 0 then ∅ else getS m S tm (j - 1)) := by
              by_cases hj0 : j = 0
              · simp only [hj0, ite_true]
              · have hne : j - 1 ≠ m := by omega
                simp only [ite_eq_right hj0]
                have : getS (m + 1) S' ⟨S, hd, tm, h⟩ (j - 1) = getS m S tm (j - 1) := by
                  simp only [getS, ite_eq_right hne]
                rw [this]
            rw [hSlow, hSj, hFj]
            exact ih S tm j hjm'

theorem getS_out_empty : ∀ (m : ℕ) (S' : Finset (Fin 4)) (t : Tiling m S')
    (j : ℕ), m ≤ j → getS m S' t j = ∅
  | 0, _, _, _, _ => rfl
  | (m + 1), S', t, j, hj => by
    have hne : j ≠ m := by omega
    have hrec : getS (m + 1) S' t j = getS m (t.1) (t.2.2.1) j :=
      getS_recurse m S' t j hne
    rw [hrec]
    exact getS_out_empty m _ _ j (by omega)

theorem getS_top_empty (m : ℕ) (t : Tiling (m + 1) ∅) :
    getS (m + 1) ∅ t m = ∅ :=
  getS_top m ∅ t

theorem getS_pred_top_empty (m : ℕ) (t : Tiling m ∅) (hm : 0 < m) :
    getS m ∅ t (m - 1) = ∅ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hsub : m' + 1 - 1 = m' := rfl
  rw [hsub]
  exact getS_top m' ∅ t

end MetaMathlibExt
end
