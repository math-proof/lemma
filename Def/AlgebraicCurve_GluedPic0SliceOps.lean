import Mathlib
import Lemma.AlgebraicCurve.GluedPic0Functoriality
import Def.AlgebraicCurve_GluedPic0Pushforward
import Lemma.ModularCurve.CharacterLatticePairings

set_option autoImplicit false

namespace AlgebraicCurve

open Finset

namespace Pic0Pair

variable {A : Type*} [AddCommGroup A]

def blockOp (a b c d : A →+ A) : A × A →+ A × A :=
  (a.coprod b).prod (c.coprod d)

@[simp]
theorem blockOp_apply (a b c d : A →+ A) (x y : A) :
    blockOp a b c d (x, y) = (a x + b y, c x + d y) := rfl


end Pic0Pair

namespace NodeData

variable {S S' : Type*} {V V' : Type*}

def perm (σ : S ≃ S') (w : S' → V) : S → V := w ∘ σ

@[simp]
theorem perm_apply (σ : S ≃ S') (w : S' → V) (s : S) : perm σ w s = w (σ s) := rfl

def map (θ : V → V') (w : S → V) : S → V' := θ ∘ w

@[simp]
theorem map_apply (θ : V → V') (w : S → V) (s : S) : map θ w s = θ (w s) := rfl

def corr [AddCommGroup V] [Fintype S'] (B : S → S' → ℤ) (w : S' → V) : S → V :=
  fun s => ∑ s', B s s' • w s'

@[simp]
theorem corr_apply [AddCommGroup V] [Fintype S'] (B : S → S' → ℤ) (w : S' → V) (s : S) :
    corr B w s = ∑ s', B s s' • w s' := rfl

variable [Fintype S] [Fintype S'] {G : Type*} [CommGroup G]


end NodeData

namespace GluedPic0

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F)


end GluedPic0

end AlgebraicCurve
