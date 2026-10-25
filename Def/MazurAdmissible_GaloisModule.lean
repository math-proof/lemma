import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.SetTheory.Cardinal.Finite
import Lemma.Compat.Mathlib430
import Structure.MazurAdmissible_GaloisModule
import Notation.MazurAdmissible_GaloisModule

set_option autoImplicit false

noncomputable section

open TensorProduct

namespace MazurAdmissible

universe u

open scoped MazurAdmissible_GaloisModule


variable {M : Type u} [AddCommGroup M]


def filtAlpha {p : ℕ} {Φ : OpenAction M} (c : AdmissibleChain p Φ) : ℕ :=
  (Finset.univ.filter fun i => c.tag i = true).card

def filtLength {p : ℕ} {Φ : OpenAction M} (c : AdmissibleChain p Φ) : ℕ := c.n

def IsMazurAdmissible (p : ℕ) (Φ : OpenAction M) : Prop :=
  Nonempty (AdmissibleChain p Φ)

def ptMul {G : Type*} [CommSemiring G] [HopfAlgebra ℤ G] (a b : G →ₐ[ℤ] Qbar) : G →ₐ[ℤ] Qbar :=
  (Algebra.TensorProduct.lift a b (fun _ _ => Commute.all _ _)).comp (Bialgebra.comulAlgHom ℤ G)

def HasFiniteFlatModelOverInt (Φ : OpenAction M) : Prop :=
  ∃ (G : Type) (_ : CommSemiring G) (_ : HopfAlgebra ℤ G) (_ : Coalgebra.IsCocomm ℤ G)
    (_ : Module.Flat ℤ G) (_ : Module.Finite ℤ G)
    (f : (G →ₐ[ℤ] Qbar) → M),
    Function.Bijective f ∧
    (∀ a b, f (ptMul a b) = f a + f b) ∧
    (∀ σ : Qbar ≃ₐ[ℚ] Qbar, ∀ a,
      f ((σ : Qbar →+* Qbar).toIntAlgHom.comp a) = Φ.φ σ (f a))

end MazurAdmissible
