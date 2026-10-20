import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RamificationInertia.ResidueGenerator
open Ideal


/--
[quotient_algebraMap_surjective_of_adjoin_singleton_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/ResidueGenerator.lean)
-/
@[path]
private lemma quotient_algebraMap_surjective_of_adjoin_singleton_eq_top_eq
  [CommRing A] [CommRing B] [Algebra A B]
  {q : Ideal B}
  {π : B}
-- given
  (hπ : π ∈ q)
  (hgen : Algebra.adjoin A {π} = ⊤) :
-- imply
  Function.Surjective (algebraMap (A ⧸ q.comap (algebraMap A B)) (B ⧸ q)) := by
-- proof
  apply Ideal.quotient_algebraMap_surjective_of_adjoin_singleton_eq_top q π hπ hgen

/--
[inertiaDeg_eq_one_of_adjoin_singleton_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RamificationInertia/ResidueGenerator.lean)
-/
@[path]
private lemma inertiaDeg_eq_one_of_adjoin_singleton_eq_top_eq
  [CommRing A] [CommRing B] [Algebra A B]
  {q : Ideal B} [q.IsMaximal] [(q.under A).IsMaximal]
  {π : B}
-- given
  (hπ : π ∈ q)
  (hgen : Algebra.adjoin A {π} = ⊤) :
-- imply
  q.inertiaDeg A = 1 := by
-- proof
  apply Ideal.inertiaDeg_eq_one_of_adjoin_singleton_eq_top q π hπ hgen


-- created on 2026-10-20
