import Mathlib
import sympy.Basic

/--
FLT-internal: the ring `AffineDilatation.Ring J a` of an affine dilatation with center `a`
over the ideal `J` (stub for the port from
[fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem)).
-/
def AffineDilatation.Ring {A : Type*} [CommRing A] (J : Ideal A) (a : A) : Type := sorry

instance {A : Type*} [CommRing A] (J : Ideal A) (a : A) : CommRing (AffineDilatation.Ring J a) := sorry

instance {A : Type*} [CommRing A] {B : Type*} [CommRing B] [Algebra B A] (J : Ideal A) (a : A) : Algebra B (AffineDilatation.Ring J a) := sorry

/--
[AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AffineDilatation_exists_algHom_surjective_ker_iff_of_surjective.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {C A : Type u} [CommRing C] [CommRing A] [Algebra R C] [Algebra R A] [Algebra C A] [IsScalarTower R C A]
  {π : R}
  {J : Ideal C}
-- given
  (hsurj : Function.Surjective (algebraMap C A)) :
-- imply
  ∃ θ' :
    AlgHom C
      (AffineDilatation.Ring J (algebraMap R C π))
      (AffineDilatation.Ring (J.map (algebraMap C A)) (algebraMap R A π)),
    Function.Surjective θ' ∧
    ∀ x : AffineDilatation.Ring J (algebraMap R C π),
      θ' x = 0 ↔ ∃ ν : ℕ, (algebraMap R _ π) ^ ν * x ∈
        (RingHom.ker (algebraMap C A)).map
          (algebraMap C (AffineDilatation.Ring J (algebraMap R C π))) :=
-- proof
  sorry


-- created on 2026-10-09
