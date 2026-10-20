/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DoldSequence.lean -/

import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Dold sequences

This file records the local trace characterization from Lemma 3 of Klaudiusz
Wójcik, *Binomial Transform and Dold Sequences*:
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Wojcik/wojcik6.tex>.
-/

namespace MetaMathlibExt

/-- An integer sequence is a Dold sequence when every finite positive prefix is
represented by traces of powers of an integer matrix of the same size.

This is the equivalent characterization in Lemma 3 of Wójcik's paper. The
ambient sequence is indexed from zero, but the defining equations begin at one,
as in the source.
-/
def IsDoldSequence (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∃ A : Matrix (Fin m) (Fin m) ℤ,
      ∀ n : ℕ, 1 ≤ n → n ≤ m → a n = Matrix.trace (A ^ n)

end MetaMathlibExt
