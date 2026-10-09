import Mathlib
import sympy.Basic
import sympy.Algebra.CommutativeAlgebra.EakinNagata

open EakinNagata

/--
[fg_of_sup_range_comap](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/CommutativeAlgebra/EakinNagata.lean)
-/
@[path]
private lemma fg_comap
  [CommRing R] [AddCommGroup M] [Module R M]
-- given
  (N : Submodule R M) (a : R)
  (h1 : (N ⊔ LinearMap.range (LinearMap.lsmul R M a)).FG)
  (h2 : (N.comap (LinearMap.lsmul R M a)).FG) :
-- imply
  N.FG := by
-- proof
  apply fg_of_sup_range_comap h1 h2


/--
[isNoetherian_of_prime_smul_top_fg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/CommutativeAlgebra/EakinNagata.lean)
-/
@[path]
private lemma cohen
  [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M]
-- given
  (hP : ∀ p : Ideal R, p.IsPrime → (p • (⊤ : Submodule R M)).FG) :
-- imply
  IsNoetherian R M := by
-- proof
  apply isNoetherian_of_prime_smul_top_fg hP


/--
[eakin_nagata](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/CommutativeAlgebra/EakinNagata.lean)
-/
@[path]
private lemma eakin
  [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] [IsNoetherianRing B]
-- given
  (hAB : Function.Injective (algebraMap A B)) :
-- imply
  IsNoetherianRing A := by
-- proof
  apply eakin_nagata hAB


-- created on 2026-10-09
