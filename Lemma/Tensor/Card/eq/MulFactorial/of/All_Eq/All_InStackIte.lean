import Mathlib
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {s : Finset (Fin n → ℤ)}
-- given
  (hn : 0 < n)
  (hswap : ∀ j : Fin n, ∀ x ∈ s,
    (fun i : Fin n => if i = ⟨0, hn⟩ then x j else if i = j then x ⟨0, hn⟩ else x i) ∈ s)
  (hcard : ∀ x ∈ s, (Finset.univ.image x).card = n) :
-- imply
  s.card = Nat.factorial n * (s.image fun x : Fin n → ℤ => Finset.univ.image x).card := by
-- proof
  classical
-- every tuple in s has distinct entries
  have hinj : ∀ x ∈ s, Function.Injective x := by
    intro x hx a b hab
    apply Finset.card_image_iff.mp _ (Finset.mem_univ a) (Finset.mem_univ b) hab
    rw [hcard x hx, Finset.card_univ, Fintype.card_fin]
-- the permutations preserving s form a subgroup
  let T : Subgroup (Equiv.Perm (Fin n)) :=
    { carrier := {σ | ∀ x ∈ s, (x ∘ ⇑σ : Fin n → ℤ) ∈ s}
      one_mem' := by
        intro x hx
        simpa using hx
      mul_mem' := by
        intro σ τ hσ hτ x hx
        have : (x ∘ ⇑(σ * τ) : Fin n → ℤ) = (x ∘ ⇑σ : Fin n → ℤ) ∘ ⇑τ := by
          funext i
          simp [Function.comp_apply]
        rw [this]
        apply hτ
        apply hσ
        assumption
      inv_mem' := by
        intro σ hσ x hx
        have hsub : s.image (fun y => (y ∘ ⇑σ : Fin n → ℤ)) ⊆ s := by
          intro y hy
          obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
          apply hσ
          assumption
        have hinj' : Set.InjOn (fun y => (y ∘ ⇑σ : Fin n → ℤ)) s := by
          intro a _ b _ hab
          funext i
          have := congr_fun hab (⇑σ⁻¹ i)
          simpa [Function.comp_apply] using this
        have heq : s.image (fun y => (y ∘ ⇑σ : Fin n → ℤ)) = s :=
          Finset.eq_of_subset_of_card_le hsub (le_of_eq (Finset.card_image_iff.mpr hinj').symm)
        have hmem : x ∈ s.image (fun y => (y ∘ ⇑σ : Fin n → ℤ)) := heq.symm ▸ hx
        obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hmem
        have : (x ∘ ⇑σ⁻¹ : Fin n → ℤ) = y := by
          funext i
          have h2 := congr_fun hyx (⇑σ⁻¹ i)
          simp [Function.comp_apply] at h2
          apply h2.symm.trans
          simp
        rw [this]
        assumption }
-- swaps of position 0 with position j preserve s
  have hmem_swap : ∀ j : Fin n, j ≠ ⟨0, hn⟩ → Equiv.swap ⟨0, hn⟩ j ∈ T := by
    intro j hj x hx
    have h : (x ∘ ⇑(Equiv.swap ⟨0, hn⟩ j) : Fin n → ℤ) =
        fun i => if i = ⟨0, hn⟩ then x j else if i = j then x ⟨0, hn⟩ else x i := by
      funext i
      if hi0 : i = ⟨0, hn⟩ then
        rw [hi0]
        simp [Equiv.swap_apply_left]
      else
        if hij : i = j then
          rw [hij]
          simp [Equiv.swap_apply_right, hj]
        else
          simp [Equiv.swap_apply_of_ne_of_ne hi0 hij, hi0, hij]
    rw [h]
    apply hswap
    assumption
-- the star transpositions generate the full symmetric group
  set S : Set (Equiv.Perm (Fin n)) := {σ | ∃ j : Fin n, j ≠ ⟨0, hn⟩ ∧ σ = Equiv.swap ⟨0, hn⟩ j} with hS_def
  have hST : S ⊆ T := by
    rintro σ ⟨j, hj, rfl⟩
    apply hmem_swap
    assumption
  have hS_swap : ∀ σ ∈ S, σ.IsSwap := by
    rintro σ ⟨j, hj, rfl⟩
    exact ⟨⟨0, hn⟩, j, Ne.symm hj, rfl⟩
  have : MulAction.IsPretransitive (Subgroup.closure S) (Fin n) := by
    rw [MulAction.isPretransitive_iff_base ⟨0, hn⟩]
    intro x
    if hx : x = ⟨0, hn⟩ then
      apply Exists.intro ⟨1, Subgroup.one_mem _⟩
      rw [← hx]
      rfl
    else
      apply Exists.intro ⟨Equiv.swap ⟨0, hn⟩ x, Subgroup.subset_closure ⟨x, hx, rfl⟩⟩
      apply Equiv.swap_apply_left
  have hgen : Subgroup.closure S = ⊤ := closure_of_isSwap_of_isPretransitive hS_swap
-- hence every permutation preserves s
  have hle : Subgroup.closure S ≤ T := by
    rwa [Subgroup.closure_le]
  have hall : ∀ σ : Equiv.Perm (Fin n), ∀ x ∈ s, (x ∘ ⇑σ : Fin n → ℤ) ∈ s := by
    intro σ
    exact hle (hgen.symm ▸ Subgroup.mem_top σ)
-- any tuple with the same image as x₀ is a permutation of x₀
  have hsub₁ : ∀ x₀ ∈ s, ∀ y ∈ s, Finset.univ.image y = Finset.univ.image x₀ →
      ∃ σ : Equiv.Perm (Fin n), (x₀ ∘ ⇑σ : Fin n → ℤ) = y := by
    intro x₀ hx₀ y hy himg
    have hyinj := hinj y hy
    have hex : ∀ i : Fin n, ∃ j : Fin n, x₀ j = y i := by
      intro i
      have hmem : y i ∈ Finset.univ.image y := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      rw [himg] at hmem
      obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hmem
      apply Exists.intro j
      assumption
    choose φ hφ using hex
    have hφinj : Function.Injective φ := fun a b hab =>
      hyinj (by rw [← hφ a, ← hφ b, hab])
    apply Exists.intro (Equiv.ofBijective φ ⟨hφinj, Finite.injective_iff_surjective.mp hφinj⟩)
    funext i
    apply hφ
-- permuting preserves the image
  have himgσ : ∀ (x₀ : Fin n → ℤ), ∀ σ : Equiv.Perm (Fin n),
      Finset.univ.image (x₀ ∘ ⇑σ : Fin n → ℤ) = Finset.univ.image x₀ := by
    intro x₀ σ
    rw [← Finset.image_image]
    rw [Finset.image_univ_of_surjective σ.surjective]
-- the fiber over the image of x₀ is the orbit of x₀
  have hfiber : ∀ x₀ ∈ s, s.filter (fun x => Finset.univ.image x = Finset.univ.image x₀) =
      Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (x₀ ∘ ⇑σ : Fin n → ℤ)) := by
    intro x₀ hx₀
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    ·
      rintro ⟨hy, himg⟩
      apply hsub₁ x₀ hx₀ y hy himg
    ·
      rintro ⟨σ, rfl⟩
      apply And.intro
      ·
        apply hall
        assumption
      ·
        apply himgσ
-- each fiber has cardinality n!
  have hcard_fiber : ∀ x₀ ∈ s,
      (s.filter (fun x => Finset.univ.image x = Finset.univ.image x₀)).card = Nat.factorial n := by
    intro x₀ hx₀
    rw [hfiber x₀ hx₀]
    have hinjσ : Function.Injective (fun σ : Equiv.Perm (Fin n) => (x₀ ∘ ⇑σ : Fin n → ℤ)) := by
      intro σ τ hστ
      apply Equiv.Perm.ext
      intro i
      apply hinj x₀ hx₀
      apply congr_fun hστ
    rw [Finset.card_image_of_injective _ hinjσ, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
-- partition s by image
  have hpart : s = (s.image fun x : Fin n → ℤ => Finset.univ.image x).biUnion
      (fun t => s.filter (fun x => Finset.univ.image x = t)) := by
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter]
    constructor
    ·
      intro hx
      exact ⟨Finset.univ.image x, ⟨x, hx, rfl⟩, hx, rfl⟩
    ·
      rintro ⟨t, ⟨y, -, rfl⟩, hx, -⟩
      assumption
  have hdisj : (↑(s.image fun x : Fin n → ℤ => Finset.univ.image x) : Set (Finset ℤ)).PairwiseDisjoint
      (fun t => s.filter (fun x => Finset.univ.image x = t)) := by
    intro t _ t' _ htt'
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_filter] at hx hx'
    apply htt'
    apply hx.2.symm.trans
    exact hx'.2
  have hsum : ∀ t ∈ s.image (fun x : Fin n → ℤ => Finset.univ.image x),
      (s.filter (fun x => Finset.univ.image x = t)).card = Nat.factorial n := by
    intro t ht
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp ht
    apply hcard_fiber
    assumption
  have hcard_eq : s.card = ((s.image fun x : Fin n → ℤ => Finset.univ.image x).biUnion
      (fun t => s.filter (fun x => Finset.univ.image x = t))).card := congr_arg _ hpart
  rw [hcard_eq, Finset.card_biUnion hdisj, Finset.sum_const_nat hsum, Nat.mul_comm]


-- created on 2026-10-07
