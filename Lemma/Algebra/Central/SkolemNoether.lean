import Mathlib
import sympy.Basic
import sympy.Algebra.Central.SkolemNoether

open SkolemNoether

/--
[tensor_simple_of_central_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Central/SkolemNoether.lean)
-/
@[main]
private lemma tensorSimple
  [Field k]
  [Ring A]
  [Algebra k A]
  [IsSimpleRing A]
  [Algebra.IsCentral k A]
  [Ring B]
  [Algebra k B]
  [IsSimpleRing B] :
-- imply
  IsSimpleRing (TensorProduct k A B) := by
-- proof
  apply tensor_simple_of_central_simple


/--
[mulLeftRight_bijective_of_central_simple](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Central/SkolemNoether.lean)
-/
@[main]
private lemma mulLeftRight_bijective
  [Field k]
  [Ring A]
  [Algebra k A]
  [FiniteDimensional k A]
  [Algebra.IsCentral k A]
  [IsSimpleRing A] :
-- imply
  Function.Bijective (AlgHom.mulLeftRight k A) := by
-- proof
  apply mulLeftRight_bijective_of_central_simple


/--
[skolem_noether](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Central/SkolemNoether.lean)
-/
@[main]
private lemma inner
  [Field k]
  [Ring A]
  [Algebra k A]
  [FiniteDimensional k A]
  [Algebra.IsCentral k A]
  [IsSimpleRing A]
-- given
  (σ : AlgEquiv k A A) :
-- imply
  ∃ u : Aˣ, ∀ x : A, σ x = (u : A) * x * (↑(u⁻¹ : Aˣ) : A) := by
-- proof
  apply skolem_noether σ


-- created on 2026-10-09
