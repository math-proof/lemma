import sympy.Basic
import Mathlib


namespace TaylorWiles

def eigenIdempotent {A : Type*} [CommRing A] (M : Matrix (Fin 2) (Fin 2) A) (b v : A) : Matrix (Fin 2) (Fin 2) A :=
  v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A))

end TaylorWiles

open TaylorWiles


@[path]
private lemma main
  [CommRing A]
-- given
  (M : Matrix (Fin 2) (Fin 2) A)
  (b v : A) :
-- imply
  eigenIdempotent M b v = v • (M - b • (1 : Matrix (Fin 2) (Fin 2) A)) := by
-- proof
  rfl


-- created on 2026-10-24
