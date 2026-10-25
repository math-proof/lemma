import Mathlib
import Lemma.HopfAlgebra.HopfKer
import Def.HopfAlgebra_HopfKerHopf
import Lemma.HopfAlgebra.FVectStructure

set_option autoImplicit false

universe u v

inductive HopfAlgebra.HasFVectDevissage (R : Type u) [CommRing R] [IsLocalRing R] (K : Type u) [Field K] [Algebra R K]
    (p : ℕ) [Fact p.Prime] : ∀ (A : Type v) [CommRing A] [HopfAlgebra K A], Prop
  | nil (A : Type v) [CommRing A] [HopfAlgebra K A] (h1 : Module.finrank K A = 1) : HasFVectDevissage R K p A
  | step (A : Type v) [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A] [Module.Finite K A]
      (Ā : Type v) [CommRing Ā] [HopfAlgebra K Ā] [Coalgebra.IsCocomm K Ā] [Module.Finite K Ā]
      (π : A →ₐc[K] Ā) (hπ : Function.Surjective π)
      (r : ℕ) [NeZero r] (F : Type) [Field F] [Fintype F] (hF : Fintype.card F = p ^ r)
      (hq : IsUnit ((p ^ r : R) - 1))
      (χ : Fˣ →* Rˣ) (ι : F →+* IsLocalRing.ResidueField R)
      (hχ : ∀ l : Fˣ, IsLocalRing.residue R (χ l : R) = ι l)
      (hrank : Module.finrank K ↥(HopfAlgebra.hopfKer π) = p ^ r)
      (σ : HopfAlgebra.FVectStructure F K ↥(HopfAlgebra.hopfKer π))
      (hĀ : HasFVectDevissage R K p Ā) : HasFVectDevissage R K p A
