import Mathlib
import Class.Mathlib_Algebra_Algebra_Hom

set_option autoImplicit false

class ContinuousSemialgHomClass (F : Type*) {R S : outParam Type*}
    [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [TopologicalSpace A] [TopologicalSpace B]
    [FunLike F A B] extends SemialgHomClass F φ A B where continuous_toFun (f : F) : Continuous f

class Pi.FiberwiseSMul {α β : Type*} (f : α → β) (R : β → Type*) (M : α → Type*)
    [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (M a)]
    [(b : β) → (σ : {a // f a = b}) → Module (R b) (M σ)]
    [Module ((b : β) → R b) ((a : α) → M a)] : Prop where
  map_smul (f R M) (r : (b : β) → R b) (x : (a : α) → M a) (b : β) (σ : {a // f a = b}) :
    (r • x) σ = r b • x σ

class Prod.IsProdSMul (R S M N : Type*) [SMul R M] [SMul S N] [SMul (R × S) (M × N)] : Prop where
  map_smul (x : R × S) (y : M × N) : x • y = (x.1 • y.1, x.2 • y.2)

open scoped RestrictedProduct

class RestrictedProduct.FiberwiseSMul {α β : Type*} (f : α → β) (R : (b : β) → Type*)
    (A : (b : β) → Set (R b)) (𝓕 : Filter β) (M : (a : α) → Type*) (B : (a : α) → Set (M a))
    (𝓖 : Filter α) [(b : β) → (σ : { a // f a = b }) → SMul (R b) (M ↑σ)]
    [SMul (Πʳ b, [R b, A b]_[𝓕]) (Πʳ a, [M a, B a]_[𝓖])] : Prop where
  map_smul (r : Πʳ b, [R b, A b]_[𝓕]) (x : Πʳ a, [M a, B a]_[𝓖]) (b : β)
    (σ : {a // f a = b}) : (r • x) σ = r b • x σ

-- ComapFiberwiseSMul deferred: needs Completion_BaseChange + RestrictedProduct_Equiv (broken in Definitions).
-- HasGaussTransport deferred in ModularCurve_GaussPencilAdapter (excluded from Class.lean).
