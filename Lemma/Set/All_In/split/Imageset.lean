import sympy.Basic


@[main]
private lemma main
  {s : Set α}
  {f : α → β} :
-- imply
  ∀ e ∈ s, f e ∈ f '' s :=
-- proof
  fun _ he => Set.mem_image_of_mem f he


-- created on 2026-09-27
