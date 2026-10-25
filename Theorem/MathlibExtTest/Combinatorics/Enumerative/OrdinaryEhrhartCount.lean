/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/OrdinaryEhrhartCount.lean -/


import Def.Combinatorics.Enumerative.OrdinaryEhrhartCount


namespace MetaMathlibExt

example (d m : ℕ) : ordinaryEhrhartCount d ∅ m = 0 := by
  simp [ordinaryEhrhartCount]

/-- A nonempty one-dimensional example exercising both dilation and the
intersection with the integer lattice. -/
example :
    ordinaryEhrhartCount 1 ({fun _ : Fin 1 => (1 : ℚ)} : Set (Fin 1 → ℚ)) 2 = 1 := by
  unfold ordinaryEhrhartCount
  have hmem :
      ((2 : ℕ) : ℚ) • (fun _ : Fin 1 => (1 : ℚ)) ∈
        Set.range (fun z : Fin 1 → ℤ => fun i => (z i : ℚ)) := by
    refine ⟨fun _ => 2, ?_⟩
    funext i
    change (2 : ℚ) = 2 * 1
    rw [mul_one]
  rw [Set.image_singleton]
  rw [Set.inter_eq_left.2 (Set.singleton_subset_iff.mpr hmem)]
  simp

end MetaMathlibExt
