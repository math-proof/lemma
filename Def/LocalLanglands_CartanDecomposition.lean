import Mathlib

open Matrix

noncomputable section

namespace LocalGL2

section CommRing

variable {R : Type*} [CommRing R]

def cartanDiag (ϖ : R) (a b : ℕ) : Matrix (Fin 2) (Fin 2) R :=
  !![ϖ ^ a, 0; 0, ϖ ^ b]


def CartanRel (g h : Matrix (Fin 2) (Fin 2) R) : Prop :=
  ∃ k₁ k₂ : (Matrix (Fin 2) (Fin 2) R)ˣ, g = k₁.val * h * k₂.val


def entryIdeal (g : Matrix (Fin 2) (Fin 2) R) : Ideal R :=
  Ideal.span (Set.range fun p : Fin 2 × Fin 2 => g p.1 p.2)


noncomputable def swapUnit : (Matrix (Fin 2) (Fin 2) R)ˣ :=
  ((Matrix.isUnit_iff_isUnit_det (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) R)).mpr
    (by simp [Matrix.det_fin_two_of])).unit

end CommRing

end LocalGL2

end
