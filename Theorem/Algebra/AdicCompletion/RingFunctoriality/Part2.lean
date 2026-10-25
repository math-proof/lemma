import Theorem.Algebra.AdicCompletion.PolynomialCompletion.Part8
import Def.Algebra.AdicCompletion.RingFunctoriality
set_option autoImplicit false


namespace AdicCompletion

universe u₀ u₁ u₂ u₃

variable {k : Type u₀} [CommRing k]

variable {R : Type u₁} {S : Type u₂} {T : Type u₃} [CommRing R] [CommRing S] [CommRing T]

variable [Algebra k R] [Algebra k S] [Algebra k T]

section LevelMap

variable (I : Ideal R) (J : Ideal S) (f : R →ₐ[k] S)

@[simp]
theorem levelMapₐ_mk (h : I.map f ≤ J) (n : ℕ) (x : R) :
    levelMapₐ I J f h n (Ideal.Quotient.mk (I ^ n) x) = Ideal.Quotient.mk (J ^ n) (f x) :=
  rfl

theorem factorPow_levelMapₐ (h : I.map f ≤ J) {m n : ℕ} (hmn : m ≤ n) (x : R ⧸ I ^ n) :
    Ideal.Quotient.factorPow J hmn (levelMapₐ I J f h n x)
      = levelMapₐ I J f h m (Ideal.Quotient.factorPow I hmn x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem levelMapₐ_id (hI : I.map (AlgHom.id k R) ≤ I) (n : ℕ) (x : R ⧸ I ^ n) :
    levelMapₐ I I (AlgHom.id k R) hI n x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem levelMapₐ_comp (h : I.map f ≤ J) (K : Ideal T) (g : S →ₐ[k] T) (hg : J.map g ≤ K)
    (hgf : I.map (g.comp f) ≤ K) (n : ℕ) (x : R ⧸ I ^ n) :
    levelMapₐ I K (g.comp f) hgf n x = levelMapₐ J K g hg n (levelMapₐ I J f h n x) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem levelMapₐ_surjective_of_surjective (h : I.map f ≤ J) (hf : Function.Surjective f)
    (n : ℕ) :
    Function.Surjective (levelMapₐ I J f h n) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨Ideal.Quotient.mk _ x, rfl⟩

end LevelMap
end AdicCompletion
