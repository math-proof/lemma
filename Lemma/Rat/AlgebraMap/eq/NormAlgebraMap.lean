import Mathlib
import sympy.Basic


/--
[Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_monoidHom_algebraMap_eq_norm_of_isIntegrallyClosed.lean)
-/
@[main]
private lemma main
  {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  {B : Type v} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
  {K : Type w} [Field K] [Algebra A K] [IsFractionRing A K]
  {L : Type w'} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] :
-- imply
  ∃ N : B →* A, ∀ b : B, algebraMap A K (N b) = Algebra.norm K (algebraMap B L b) := by
-- proof
  classical

  have hmem : ∀ b : B, ∃ a : A, algebraMap A K a = Algebra.norm K (algebraMap B L b) := by
    intro b
    have hb : IsIntegral A (algebraMap B L b) := (Algebra.IsIntegral.isIntegral (R := A) b).algebraMap
    have hn : IsIntegral A (Algebra.norm K (algebraMap B L b)) := Algebra.isIntegral_norm K hb
    exact IsIntegrallyClosed.isIntegral_iff.mp hn
  choose N hN using hmem
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  refine ⟨{ toFun := N, map_one' := ?_, map_mul' := ?_ }, fun b => hN b⟩
  · apply hinj
    rw [hN, map_one, map_one, map_one]
  · intro b c
    apply hinj
    rw [hN, map_mul, map_mul, map_mul, hN, hN]


-- created on 2026-10-05
