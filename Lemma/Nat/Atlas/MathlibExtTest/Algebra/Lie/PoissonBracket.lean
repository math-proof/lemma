import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Algebra.Lie.PoissonBracket
open MathlibExtTest MathlibExtTest.Algebra MathlibExtTest.Algebra.Lie MathlibExtTest.Algebra.Lie.PoissonBracket
open MathlibExt.Algebra.Lie.PoissonBracket


namespace MathlibExtTest.Algebra.Lie.PoissonBracket

/--
[trivial_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/PoissonBracket.lean)
-/
@[path]
lemma trivial_poisson
  {A : Type}
  [CommRing A]
  [Algebra ℂ A]
  {P : Ideal A} :
-- imply
  IsPoissonIdeal A (trivialBracket A) P :=
-- proof
  fun a p _ => P.zero_mem

end MathlibExtTest.Algebra.Lie.PoissonBracket

namespace MathlibExtTest.Algebra.Lie.PoissonBracket

/--
[trivial_core_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Algebra/Lie/PoissonBracket.lean)
-/
@[path]
lemma trivial_core_top
  {A : Type}
  [CommRing A]
  [Algebra ℂ A] :
-- imply
  poissonCore A (trivialBracket A) ⊤ = ⊤ := by
-- proof
  apply le_antisymm (poissonCore_le A (trivialBracket A) ⊤)
  exact le_poissonCore A (trivialBracket A)
    ⟨le_rfl, trivial_poisson A ⊤⟩

end MathlibExtTest.Algebra.Lie.PoissonBracket


-- created on 2026-10-23
