import sympy.Basic


@[path]
private lemma main
  {s : Finset ℝ}
  {e d : ℝ}
-- given
  (hd : d ≠ 0) :
-- imply
  e ∈ s ↔ e * d ∈ Finset.image (fun x => x * d) s := by
-- proof
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨e, h, rfl⟩
  · intro h
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
    have hye : y = e := mul_right_cancel₀ hd hxy
    rw [hye] at hy
    exact hy


-- created on 2023-05-30
