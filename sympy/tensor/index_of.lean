import sympy.Basic

/-!
SymPy's `index[v](x[:n])` (`Lemma/Finset/Eq/of/Eq/index/indexOf_Get.py`): the first position of the value `v`
among `x[0], …, x[n-1]`, and `n` when `v` does not occur (the `List.idxOf` convention).
-/

namespace IndexOf

def index {α : Type*} [DecidableEq α] (v : α) (x : ℕ → α) (n : ℕ) : ℕ :=
  ((List.range n).map x).idxOf v

theorem index_lt {α : Type*} [DecidableEq α] {v : α} {x : ℕ → α} {n : ℕ} (h : ∃ j < n, x j = v) :
    index v x n < n := by
  obtain ⟨j, hj, rfl⟩ := h
  have hm : x j ∈ (List.range n).map x := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  simpa [index] using List.idxOf_lt_length_of_mem hm

theorem get_index {α : Type*} [DecidableEq α] {v : α} {x : ℕ → α} {n : ℕ} (h : ∃ j < n, x j = v) :
    x (index v x n) = v := by
  obtain ⟨j, hj, rfl⟩ := h
  have hm : x j ∈ (List.range n).map x := List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
  have e := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
  simp only [List.getElem_map, List.getElem_range] at e
  exact e

theorem index_get {α : Type*} [DecidableEq α] (x : ℕ → α) (n : ℕ) (hx : Set.InjOn x ↑(Finset.range n))
    {j : ℕ} (hj : j < n) : index (x j) x n = j := by
  have hnd : ((List.range n).map x).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => hx (Finset.mem_coe.mpr (Finset.mem_range.mpr (List.mem_range.mp ha)))
      (Finset.mem_coe.mpr (Finset.mem_range.mpr (List.mem_range.mp hb))) e) List.nodup_range
  have hlen : j < ((List.range n).map x).length := by simpa using hj
  simpa [index] using hnd.idxOf_getElem j hlen

end IndexOf
