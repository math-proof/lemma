/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Data.List.FinRange
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Ring
import Def.Combinatorics.BellPermutationsSecondKind.Part3


namespace MetaMathlibExt

theorem ext_castSucc {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) (j : Fin n) :
    ext g v j.castSucc = (g j).castSucc := by
  simp [ext, Fin.snoc_castSucc]

theorem ext_last {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) :
    ext g v (Fin.last n) = v := by
  simp [ext, Fin.snoc_last]

theorem image_ext {n : ℕ} (g : Fin n → Fin n) (v : Fin (n + 1)) :
    Finset.univ.image (ext g v) = insert v ((Finset.univ.image g).image Fin.castSucc) := by
  apply Finset.ext
  intro w
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => left; rw [ext_last] at hi; exact hi.symm
    | cast j => right; rw [ext_castSucc] at hi; exact ⟨g j, ⟨j, rfl⟩, hi⟩
  · rintro (hv | ⟨y, ⟨j, hj⟩, hy⟩)
    · exact ⟨Fin.last n, by rw [ext_last]; exact hv.symm⟩
    · exact ⟨j.castSucc, by rw [ext_castSucc, hj, hy]⟩

theorem card_castImg {n : ℕ} (g : Fin n → Fin n) :
    ((Finset.univ.image g).image Fin.castSucc).card = numVals g := by
  unfold numVals
  rw [Finset.card_image_of_injective _ (Fin.castSucc_injective n)]

theorem v_mem_castImg {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1)) :
    v ∈ (Finset.univ.image g).image Fin.castSucc ↔ v.val < numVals g := by
  constructor
  · intro hv
    rw [Finset.mem_image] at hv
    obtain ⟨y, hy, hyv⟩ := hv
    have hval : v.val = y.val := by rw [← hyv]; exact Fin.val_castSucc y
    have hy' : y.val < numVals g := (rgf_mem_image hg y).mp hy
    omega
  · intro hlt
    have hvn : v.val < n := lt_of_lt_of_le hlt (numVals_le g)
    rw [Finset.mem_image]
    exact ⟨⟨v.val, hvn⟩, (rgf_mem_image hg ⟨v.val, hvn⟩).mpr hlt, Fin.ext rfl⟩

theorem numVals_ext_lt {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1))
    (hv : v.val < numVals g) : numVals (ext g v) = numVals g := by
  change (Finset.univ.image (ext g v)).card = numVals g
  rw [image_ext, Finset.insert_eq_self.mpr ((v_mem_castImg hg v).mpr hv)]
  exact card_castImg g

theorem numVals_ext_eq {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1))
    (hv : v.val = numVals g) : numVals (ext g v) = numVals g + 1 := by
  change (Finset.univ.image (ext g v)).card = numVals g + 1
  rw [image_ext, Finset.card_insert_of_notMem (by rw [v_mem_castImg hg v]; omega), card_castImg g]

theorem ext_rgf {n : ℕ} {g : Fin n → Fin n} (hg : IsRGF g) (v : Fin (n + 1))
    (hv : v.val ≤ numVals g) : IsRGF (ext g v) := by
  intro i j hj
  induction i using Fin.lastCases with
  | last =>
    rw [ext_last] at hj
    have hjn : j.val < n := by
      have := numVals_le g; omega
    have hmem : (⟨j.val, hjn⟩ : Fin n) ∈ Finset.univ.image g :=
      (rgf_mem_image hg ⟨j.val, hjn⟩).mpr (by change j.val < numVals g; omega)
    rw [Finset.mem_image] at hmem
    obtain ⟨a, _, ha⟩ := hmem
    refine ⟨a.castSucc, ?_, ?_⟩
    · rw [Fin.val_castSucc]; exact a.isLt.trans_le (by simp)
    · rw [ext_castSucc, ha]; exact Fin.ext rfl
  | cast b =>
    rw [ext_castSucc] at hj
    have hjn : j.val < n := by
      have := (g b).isLt; rw [Fin.val_castSucc] at hj; omega
    rw [Fin.val_castSucc] at hj
    obtain ⟨a₀, ha₀lt, ha₀⟩ := hg b ⟨j.val, hjn⟩ (by exact hj)
    refine ⟨a₀.castSucc, ?_, ?_⟩
    · rw [Fin.val_castSucc, Fin.val_castSucc]; exact ha₀lt
    · rw [ext_castSucc, ha₀]; exact Fin.ext rfl

end MetaMathlibExt
