/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Def.Combinatorics.BellPermutationsSecondKind.Part4


namespace MetaMathlibExt

theorem restr_castSucc {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) (i : Fin n) :
    Fin.castSucc (restr f hf i) = f i.castSucc := by
  apply Fin.ext; simp [restr]

theorem decomp {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) :
    f = ext (restr f hf) (f (Fin.last n)) := by
  funext i
  induction i using Fin.lastCases with
  | last => rw [ext_last]
  | cast j => rw [ext_castSucc, restr_castSucc]

theorem restr_rgf {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) : IsRGF
    (restr f hf) := by
  intro i j' hj'
  have hj'2 : (j'.castSucc).val < (f i.castSucc).val := by
    rw [Fin.val_castSucc]; exact hj'
  obtain ⟨i₀, hi₀lt, hi₀⟩ := hf i.castSucc j'.castSucc hj'2
  rw [Fin.val_castSucc] at hi₀lt
  refine ⟨⟨i₀.val, lt_trans hi₀lt i.isLt⟩, hi₀lt, ?_⟩
  apply Fin.ext
  show (restr f hf ⟨i₀.val, _⟩).val = j'.val
  have : (⟨i₀.val, lt_trans hi₀lt i.isLt⟩ : Fin n).castSucc = i₀ := Fin.ext (by simp)
  simp only [restr]
  rw [this, hi₀, Fin.val_castSucc]

theorem restr_ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) (hf : IsRGF (ext g v)) :
    restr (ext g v) hf = g := by
  funext i
  apply Fin.ext
  change (ext g v i.castSucc).val = (g i).val
  rw [ext_castSucc, Fin.val_castSucc]

theorem last_le {n : ℕ} (f : Fin (n + 1) → Fin (n + 1)) (hf : IsRGF f) :
    (f (Fin.last n)).val ≤ numVals (restr f hf) := by
  by_contra hc
  rw [not_le] at hc
  have hbnd : numVals (restr f hf) < n := by
    have := rgf_subdiag hf (Fin.last n)
    simp only [Fin.val_last] at this
    omega
  have hjval : (⟨numVals (restr f hf), by omega⟩ : Fin (n+1)).val < (f (Fin.last n)).val := by
    simpa using hc
  obtain ⟨i₀, _, hi₀⟩ := hf (Fin.last n) ⟨numVals (restr f hf), by omega⟩ hjval
  have hi₀n : i₀.val < n := by
    have := i₀.isLt; omega
  have hmem : (⟨numVals (restr f hf), hbnd⟩ : Fin n) ∈ Finset.univ.image (restr f hf) := by
    rw [Finset.mem_image]
    refine ⟨⟨i₀.val, hi₀n⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    change (restr f hf ⟨i₀.val, hi₀n⟩).val = numVals (restr f hf)
    have hcs : (⟨i₀.val, hi₀n⟩ : Fin n).castSucc = i₀ := Fin.ext (by simp)
    simp only [restr]
    rw [hcs, hi₀]
  rw [rgf_mem_image (restr_rgf f hf)] at hmem
  simp at hmem

end MetaMathlibExt
