import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


private lemma lastEquiv_eval
  {n : ℕ} [CommSemiring R]
  (x : Fin n → R)
  (y : R)
  (P : MvPolynomial (Fin (n + 1)) R) :
    MvPolynomial.eval (Fin.lastCases y x) P =
      eval y (map (MvPolynomial.eval x) (rothLastEquiv R n P)) := by
  have h := MvPolynomial.optionEquivLeft_elim_eval R (Fin n) x y
    ((MvPolynomial.renameEquiv R finSuccEquivLast) P)
  rw [MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename] at h
  change MvPolynomial.eval _ P = _ at h
  have hfun : (fun z : Fin (n + 1) ↦ Fin.lastCases y x z) =
    (fun z : Option (Fin n) ↦ z.elim y x) ∘ finSuccEquivLast := by
    funext z
    refine Fin.lastCases ?_ (fun j ↦ ?_) z <;> simp
  rw [hfun]
  simpa [rothLastEquiv] using h

/--
[rothMvHasse_eval_last_of_factorization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  (P : MvPolynomial (Fin (n + 1)) ℚ)
  (V : MvPolynomial (Fin n) ℚ)
  (W : ℚ[X])
-- given
  (hfactor : rothLastEquiv ℚ n P =
    C V * map MvPolynomial.C W)
  (x : Fin n → ℚ)
  (y : ℚ)
  (i : RothMvIndex n)
  (a : ℕ) :
-- imply
  MvPolynomial.eval (Fin.lastCases y x)
    (rothMvHasse (rothLastIndex i a) P) =
    MvPolynomial.eval x (rothMvHasse i V) *
      (hasseDeriv a W).eval y := by
-- proof
  let phi : Fin 1 → MvPolynomial (Fin n) ℚ := fun _ ↦ V
  let psi : Fin 1 → ℚ[X] := fun _ ↦ W
  have hdecomp : rothLastEquiv ℚ n P =
      ∑ j, C (phi j) * map MvPolynomial.C (psi j) := by
    rw [hfactor]
    simp [phi, psi]
  have hhasse :=
    RothLastEquiv.eq.Sum_MulCMap.of.RothMvIndex.Eq_Sum_MulCMapC
      (rothLastEquiv ℚ n P) phi psi hdecomp i a
  have hhasse' :
    rothLastEquiv ℚ n (rothMvHasse (rothLastIndex i a) P) =
      C (rothMvHasse i V) *
        map MvPolynomial.C (hasseDeriv a W) := by
    simpa [phi, psi] using hhasse
  have hcomp : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id ℚ := by
    ext z
    simp
  rw [lastEquiv_eval, hhasse', Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_map, hcomp, Polynomial.map_id, Polynomial.eval_mul,
    Polynomial.eval_C]


-- created on 2026-10-21
