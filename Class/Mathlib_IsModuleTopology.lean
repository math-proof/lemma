import Mathlib

section

open Topology

variable (R : Type*) [Ring R] [TopologicalSpace R]
  (M : Type*) [AddCommGroup M] [Module R M] [TopologicalSpace M]

class IsTopologicalModule extends ContinuousSMul R M, ContinuousAdd M

end

class IsBiscalar (R S : Type*) {A B : Type*} [Semiring R] [Semiring S] [AddCommMonoid A]
    [AddCommMonoid B] [Module R A] [Module R B] [Module S A] [Module S B] (f : A → B) where
  map_smul₁ : ∀ (r : R) (a : A), f (r • a) = r • f a
  map_smul₂ : ∀ (s : S) (a : A), f (s • a) = s • f a
