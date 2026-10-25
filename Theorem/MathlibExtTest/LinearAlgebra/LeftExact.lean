/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/LinearAlgebra/LeftExact.lean -/

import Lemma.Matrix.LeftExact
universe u v w

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]
variable {P : Type w} [AddCommGroup P] [Module R P]


-- (1) Forward: exact/surjective pair gives Hom injectivity and exactness.
example (f : M →ₗ[R] N) (g : N →ₗ[R] P) (hE : Function.Exact f g)
    (hS : Function.Surjective g) (D : Type w) [AddCommGroup D]
    [Module R D] :
    Function.Injective (LinearMap.lcomp R D g) ∧
      Function.Exact (LinearMap.lcomp R D g)
        (LinearMap.lcomp R D f) := by
  obtain ⟨hInj, hEx⟩ :=
    (LinearMap.exact_and_surjective_iff_forall_lcomp f g).mp ⟨hE, hS⟩ D
  exact ⟨hInj, hEx⟩

-- (2) Recover original exactness from quantified Hom hypothesis.
example (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hH : ∀ D : Type w, ∀ [AddCommGroup D] [Module R D],
      Function.Injective (LinearMap.lcomp R D g) ∧
        Function.Exact (LinearMap.lcomp R D g)
          (LinearMap.lcomp R D f)) :
    Function.Exact f g :=
  ((LinearMap.exact_and_surjective_iff_forall_lcomp f g).mpr hH).1

-- (3) Recover original surjectivity from quantified Hom hypothesis.
example (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hH : ∀ D : Type w, ∀ [AddCommGroup D] [Module R D],
      Function.Injective (LinearMap.lcomp R D g) ∧
        Function.Exact (LinearMap.lcomp R D g)
          (LinearMap.lcomp R D f)) :
    Function.Surjective g :=
  ((LinearMap.exact_and_surjective_iff_forall_lcomp f g).mpr hH).2

-- (4) Concrete split pair, then forward to arbitrary D.
example (R : Type u) [CommRing R] (D : Type u) [AddCommGroup D]
    [Module R D] :
    Function.Injective
        (LinearMap.lcomp R D (LinearMap.snd R R R)) ∧
      Function.Exact
        (LinearMap.lcomp R D (LinearMap.snd R R R))
        (LinearMap.lcomp R D (LinearMap.inl R R R)) := by
  have hE : Function.Exact (LinearMap.inl R R R)
      (LinearMap.snd R R R) := by
    rw [LinearMap.exact_iff]
    ext x
    simp only [LinearMap.mem_ker, LinearMap.mem_range]
    obtain ⟨a, b⟩ := x
    constructor
    · intro h
      have hb : b = 0 := by simpa using h
      subst hb
      exact ⟨a, by simp⟩
    · rintro ⟨y, hy⟩
      have h2 := congrArg (LinearMap.snd R R R) hy
      simpa using h2.symm
  have hS : Function.Surjective (LinearMap.snd R R R) :=
    LinearMap.snd_surjective
  obtain ⟨hInj, hEx⟩ :=
    (LinearMap.exact_and_surjective_iff_forall_lcomp
      (LinearMap.inl R R R) (LinearMap.snd R R R)).mp ⟨hE, hS⟩ D
  exact ⟨hInj, hEx⟩

