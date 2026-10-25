import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.VarietyAlgebraEquiv.Part2
open MvPolynomial


variable (k : Type*) [Field k]
/--
[bind₁_mem_idealOfAlgebraicSet_of_maps_to](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
lemma bind₁_mem_idealOfAlgebraicSet_of_maps_to {m n : ℕ}
  {X : Set (AffineSpace_k k m)} {Y : Set (AffineSpace_k k n)}
  (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
  (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
  {f : MvPolynomial (Fin n) (AlgebraicClosure k)}
  (hf : f ∈ idealOfAlgebraicSet Y) :
  (MvPolynomial.bind₁ polys) f ∈ idealOfAlgebraicSet X := by
  intro P hP
  have key : MvPolynomial.eval P ((MvPolynomial.bind₁ polys) f) =
    MvPolynomial.eval (polyMapEval k m n polys P) f := by
    simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
    rfl
  rw [key]
  exact hf _ (hmaps P hP)

/--
[AffineMorphism.pullback_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
lemma AffineMorphism.pullback_eval
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y}
  {g : MvPolynomial (Fin n) (AlgebraicClosure k)}
  {P : AffineSpace_k k m}
-- given
  (hP : P ∈ X) :
-- imply
  evalOnCoordRing k X P hP (φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) = evalOnCoordRing k Y (φ.toFun k P) (φ.maps_to P hP) (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g) := by
-- proof
  simp only [pullback_mk, evalOnCoordRing_mk]
  simp only [MvPolynomial.eval, MvPolynomial.eval₂Hom_bind₁]
  rfl

/--
[evalOnCoordRing_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
private lemma evalOnCoordRing_mk_eq
  {k : Type*}
  [Field k]
  {n : ℕ}
  {X : Set (Fin n → AlgebraicClosure k)}
  {P : Fin n → AlgebraicClosure k}
  {g : MvPolynomial (Fin n) (AlgebraicClosure k)}
-- given
  (hP : P ∈ X) :
-- imply
  evalOnCoordRing k X P hP (Ideal.Quotient.mk (idealOfAlgebraicSet X) g) = MvPolynomial.eval P g := by
-- proof
  apply evalOnCoordRing_mk k X P hP g

/--
[bind](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
private lemma bind_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {f : MvPolynomial (Fin n) (AlgebraicClosure k)}
-- given
  (hmaps : ∀ P ∈ X, polyMapEval k m n polys P ∈ Y)
  (hf : f ∈ idealOfAlgebraicSet Y) :
-- imply
  (MvPolynomial.bind₁ polys) f ∈ idealOfAlgebraicSet X := by
-- proof
  apply bind k polys hmaps hf

/--
[AffineMorphism.pullback_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
private lemma pullback_mk_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {φ : AffineMorphism k m n X Y}
  {g : MvPolynomial (Fin n) (AlgebraicClosure k)} :
-- imply
  φ.pullback k (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g) = Ideal.Quotient.mk (idealOfAlgebraicSet X) ((MvPolynomial.bind₁ φ.polys) g) := by
-- proof
  apply AffineMorphism.pullback_mk k φ g

/--
[ringHom_eq_eval_of_alg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
private lemma ringHom_eq_eval_of_alg_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X}
  {polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)}
  {P : AffineSpace_k k m}
-- given
  (hθ_alg : ∀ r : AlgebraicClosure k, θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) = Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))
  (hpolys : ∀ j : Fin n, Ideal.Quotient.mk (idealOfAlgebraicSet X) (polys j) = θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)))
  (hP : P ∈ X) :
-- imply
  ((evalOnCoordRing k X P hP).comp (θ.comp (Ideal.Quotient.mk (idealOfAlgebraicSet Y)))) = MvPolynomial.eval (polyMapEval k m n polys P) := by
-- proof
  apply ringHom_eq_eval_of_alg k θ hθ_alg polys hpolys P hP

/--
[algebraHom_induces_morphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
private lemma algebraHom_induces_morphism_eq
  {k : Type*}
  [Field k]
  {m n : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {θ : AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X}
-- given
  (hY : Y = AlgebraicSet k n (idealOfAlgebraicSet Y : Set _))
  (hθ_alg : ∀ r : AlgebraicClosure k, θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) = Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r)) :
-- imply
  ∃ (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k)), (∀ P ∈ X, polyMapEval k m n polys P ∈ Y) ∧ (∀ (g : MvPolynomial (Fin n) (AlgebraicClosure k)) (P : AffineSpace_k k m) (hP : P ∈ X), evalOnCoordRing k X P hP (θ (Ideal.Quotient.mk (idealOfAlgebraicSet Y) g)) = MvPolynomial.eval (polyMapEval k m n polys P) g) := by
-- proof
  apply algebraHom_induces_morphism k hY θ hθ_alg

/--
[AffineMorphism.pullback_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/VarietyAlgebraEquiv.lean)
-/
@[path]
private lemma pullback_comp_eq
  {k : Type*}
  [Field k]
  {m n r : ℕ}
  {X : Set (AffineSpace_k k m)}
  {Y : Set (AffineSpace_k k n)}
  {Z : Set (AffineSpace_k k r)}
  {ψ : AffineMorphism k n r Y Z}
  {φ : AffineMorphism k m n X Y} :
-- imply
  (ψ.comp k φ).pullback k = (φ.pullback k).comp (ψ.pullback k) := by
-- proof
  apply AffineMorphism.pullback_comp k ψ φ


-- created on 2026-10-23
