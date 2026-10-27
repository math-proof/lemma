import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.HopfAlgebra.HopfKer
open HopfAlgebra


private lemma  finite
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R]
  {A : Type v}
  [CommRing A]
  [Bialgebra R A]
  [Module.Finite R A]
  [Module.Free R A]
  {B : Type w}
  [CommRing B]
  [Bialgebra R B]
  (π : BialgHom R A B)
  : Module.Finite R ↥(hopfKer π) := by
  have : IsNoetherianRing R := inferInstance
  have : IsNoetherian R A := isNoetherian_of_isNoetherianRing_of_finite R A
  exact Module.Finite.of_injective (Subalgebra.val (hopfKer π)).toLinearMap Subtype.val_injective

private lemma  free
  {R : Type u}
  [CommRing R]
  [IsDomain R]
  [IsPrincipalIdealRing R]
  {A : Type v}
  [CommRing A]
  [Bialgebra R A]
  [Module.Finite R A]
  [Module.Free R A]
  {B : Type w}
  [CommRing B]
  [Bialgebra R B]
  (π : BialgHom R A B)
  : Module.Free R ↥(hopfKer π) := by
  have := finite π
  exact Module.free_of_finite_type_torsion_free'
/--
[HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
  {B : Type w} [CommRing B] [Bialgebra R B]
  {π : BialgHom R A B} :
-- imply
  Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Free R ↥(HopfAlgebra.hopfKer π) :=
-- proof
  ⟨finite π, free π⟩


-- created on 2026-10-24
