import sympy.Basic


@[main]
private lemma main
  {s : Finset ℝ}
  {e d : ℝ}
-- given
  (h₀ : d ≠ 0)
  (h : e ∈ s) :
-- imply
  e * d ∈ Finset.image (fun x => x * d) s := by
-- proof
  exact Finset.mem_image.mpr ⟨e, h, rfl⟩


-- created on 2023-05-30
