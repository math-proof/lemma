import Mathlib
import sympy.Basic
import sympy.Algebra.Lie.PoissonBracket

open Poisson

/--
[bracket_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma zero_bracket
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) (a : A) :
-- imply
  br.bracket a 0 = 0 := by
-- proof
  apply bracket_zero


/--
[bot_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma poisson_bot
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) :
-- imply
  IsPoissonIdeal A br ⊥ := by
-- proof
  apply bot_poisson


/--
[sup_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma poisson_sup
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) (I J K : Ideal A)
  (hI : I ≤ J ∧ IsPoissonIdeal A br I)
  (hK : K ≤ J ∧ IsPoissonIdeal A br K) :
-- imply
  I ⊔ K ≤ J ∧ IsPoissonIdeal A br (I ⊔ K) := by
-- proof
  apply sup_poisson br hI hK


/--
[poissonCore_poisson](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma core_poisson
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) (J : Ideal A) :
-- imply
  IsPoissonIdeal A br (poissonCore A br J) := by
-- proof
  apply poissonCore_poisson


/--
[poissonCore_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma core_le
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) (J : Ideal A) :
-- imply
  poissonCore A br J ≤ J := by
-- proof
  apply poissonCore_le


/--
[le_poissonCore](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma le_core
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) (J P : Ideal A) (hP : P ≤ J ∧ IsPoissonIdeal A br P) :
-- imply
  P ≤ poissonCore A br J := by
-- proof
  apply le_poissonCore (br := br) (hP := hP)


/--
[poissonCore_isGreatest](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/Lie/PoissonBracket.lean)
-/
@[main]
private lemma core_greatest
  [CommRing A] [Algebra ℂ A]
-- given
  (br : PoissonBracket A) (J : Ideal A) :
-- imply
  IsGreatest {P : Ideal A | P ≤ J ∧ IsPoissonIdeal A br P}
    (poissonCore A br J) := by
-- proof
  apply poissonCore_isGreatest


-- created on 2026-10-09
