import Lemma.Basic


@[main, comm, mp, mpr]
private lemma main
-- given
  (x : α)
  (s : ι → Set α) :
-- imply
  x ∈ ⋂ i, s i ↔ ∀ i, x ∈ s i :=
-- proof
  Set.mem_iInter


@[main, comm, mp, mpr]
private lemma set
-- given
  (x : α)
  (s : Set ι)
  (f : ι → Set α) :
-- imply
  x ∈ ⋂ i ∈ s, f i ↔ ∀ i ∈ s, x ∈ f i := by
-- proof
  simp


@[main, comm, mp, mpr]
private lemma double
  {ι : Sort u}
  {κ : ι → Sort v}
-- given
  (x : γ)
  (s : (i : ι) → κ i → Set γ) :
-- imply
  x ∈ ⋂ i : ι, ⋂ j : κ i, s i j ↔ ∀ i j, x ∈ s i j :=
-- proof
  Set.mem_iInter₂


@[main, comm, mp, mpr]
private lemma set₂
  {κ : ι → Type u}
-- given
  (x : γ)
  (s_i : Set ι)
  (s_j : (i : ι) → Set (κ i))
  (f : (i : ι) → κ i → Set γ) :
-- imply
  x ∈ ⋂ i ∈ s_i, ⋂ j ∈ s_j i, f i j ↔ ∀ i ∈ s_i, ∀ j ∈ s_j i, x ∈ f i j := by
-- proof
  simp


-- created on 2025-08-02
