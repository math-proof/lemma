import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct
open IsLocalRing


attribute [local instance] Algebra.TensorProduct.rightAlgebra


/--
[Algebra_FormallyUnramified_of_residueField_baseChange_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallyUnramified_of_residueField_baseChange_of_finite.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
-- given
  (h : Algebra.FormallyUnramified (ResidueField R) (ResidueField R ⊗[R] S)) :
-- imply
  Algebra.FormallyUnramified R S := by
-- proof
  have : Module.Finite S Ω[S⁄R] := inferInstance
  have : Module.Finite R Ω[S⁄R] := Module.Finite.trans S _
  have e := KaehlerDifferential.tensorKaehlerEquivBase R (ResidueField R) S (ResidueField R ⊗[R] S)
  have : Subsingleton Ω[(ResidueField R ⊗[R] S)⁄(ResidueField R)] :=
    h.subsingleton_kaehlerDifferential
  have : Subsingleton (ResidueField R ⊗[R] Ω[S⁄R]) := e.toEquiv.subsingleton
  refine ⟨(subsingleton_tensorProduct (R := R) (M := Ω[S⁄R])).mp inferInstance⟩


-- created on 2026-10-12
