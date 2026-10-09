import Mathlib
import sympy.Basic


/--
[Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_finite_quotient_of_isMaximal_of_finiteType_of_finite_quotient.lean)
-/
@[path]
private lemma main
  [CommRing A] [CommRing B] [Algebra A B] [Algebra.FiniteType A B]
  {𝔪 : Ideal A} [𝔪.IsMaximal] [Finite (A ⧸ 𝔪)]
  {𝔭 : Ideal B} [𝔭.IsMaximal]
-- given
  (h𝔪 : Ideal.map (algebraMap A B) 𝔪 ≤ 𝔭) :
-- imply
  Finite (B ⧸ 𝔭) := by
-- proof
  classical
  let : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  let : Field (B ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  have hle : 𝔪 ≤ 𝔭.comap (algebraMap A B) := Ideal.map_le_iff_le_comap.mp h𝔪
  let f : A ⧸ 𝔪 →+* B ⧸ 𝔭 := Ideal.quotientMap 𝔭 (algebraMap A B) hle
  let : Algebra (A ⧸ 𝔪) (B ⧸ 𝔭) := f.toAlgebra
  have : IsScalarTower A (A ⧸ 𝔪) (B ⧸ 𝔭) :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have : Algebra.FiniteType A (B ⧸ 𝔭) := inferInstance
  have : Algebra.FiniteType (A ⧸ 𝔪) (B ⧸ 𝔭) := Algebra.FiniteType.of_restrictScalars_finiteType A _ _
  have : Module.Finite (A ⧸ 𝔪) (B ⧸ 𝔭) := finite_of_finite_type_of_isJacobsonRing _ _
  exact Module.finite_of_finite (A ⧸ 𝔪)


-- created on 2026-10-05
