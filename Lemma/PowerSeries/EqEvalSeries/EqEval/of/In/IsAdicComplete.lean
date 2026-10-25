import Mathlib
import sympy.Basic
import Lemma.FormalGroup.NSeries
open FormalGroup


/-- ported from external source -/

private lemma  aux {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [uR : UniformSpace R] [DiscreteUniformity R]
  [UniformSpace A] [IsUniformAddGroup A] [CompleteSpace A] [T2Space A]
  [IsTopologicalRing A] [IsLinearTopology A A]
  (x : A) (hx : IsTopologicallyNilpotent x) :
  ∃ e : PowerSeries R →+* A,
    (∀ f : PowerSeries R, FormalGroup.evalSeries f x = e f) ∧
    (∀ p : Polynomial R, e (p : PowerSeries R) = Polynomial.eval₂ (algebraMap R A) x p) := by
  have : DiscreteTopology R := inferInstance
  have hφ : Continuous (algebraMap R A) := continuous_of_discreteTopology
  have ha : PowerSeries.HasEval x := (PowerSeries.hasEval_def x).mpr hx
  refine ⟨PowerSeries.eval₂Hom hφ ha, fun f => ?_, fun p => ?_⟩
  · rw [FormalGroup.evalSeries_eq_eval₂, PowerSeries.coe_eval₂Hom]
  · rw [PowerSeries.coe_eval₂Hom, PowerSeries.eval₂_coe]
@[path]
private lemma main
  [CommRing T]
  {I : Ideal T}
  {x : T}
-- given
  (h : IsAdicComplete I T)
  (hx : x ∈ I) :
-- imply
  ∃ e : PowerSeries T →+* T,
      (∀ f : PowerSeries T, (let : WithIdeal T :=
  ⟨I⟩; FormalGroup.evalSeries f x) = e f) ∧
        (∀ p : Polynomial T, e (p : PowerSeries T) = p.eval x) := by
-- proof
    let wi : WithIdeal T := ⟨I⟩
    have hI : IsAdic I := rfl
    obtain ⟨hc, ht2⟩ := hI.isAdicComplete_iff.mp h
    have hxn : IsTopologicallyNilpotent x := WithIdeal.isTopologicallyNilpotent_of_mem hx
    obtain ⟨e, he, hp⟩ := @aux T T _ _ (Algebra.id T) ⊥ inferInstance
      (WithIdeal.instUniformSpace T) inferInstance hc ht2 inferInstance inferInstance x hxn
    refine ⟨e, he, fun p => ?_⟩
    rw [hp p, Polynomial.eval₂_eq_eval_map]
    simp [Polynomial.map_id]


-- created on 2026-10-23
