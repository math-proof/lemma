import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma Polynomial.mem_range_of_eval_eq_const {F L : Type u} [Field F] [Field L] [Algebra F L] (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card) (hval : ∀ y ∈ s, Polynomial.aeval y g = x) : x ∈ (algebraMap F L).range := by
  classical
  set i := algebraMap F L
  set Q : Polynomial L := g.map i - Polynomial.C x with hQ
  have hQdeg : Q.natDegree ≤ g.natDegree := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q s (fun y hy => ?_) (hQdeg.trans_lt hcard)
    rw [hQ, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map_algebraMap, hval y hy, sub_self]
  have hconst : g.map i = Polynomial.C x := sub_eq_zero.mp hQ0
  refine ⟨g.coeff 0, ?_⟩
  have := congrArg (fun P : Polynomial L => P.coeff 0) hconst
  simpa only [Polynomial.coeff_map, Polynomial.coeff_C_zero] using this
/--
[Polynomial_mem_range_of_eval_eq_const](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_mem_range_of_eval_eq_const.lean)
-/
@[path]
private lemma main
  {F L : Type u} [Field F] [Field L] [Algebra F L]
  (g : Polynomial F)
  (x : L)
  (s : Finset L)
  -- given
  (hcard : g.natDegree < s.card)
  (hval : ∀ y ∈ s, Polynomial.aeval y g = x) :
  -- imply
  x ∈ (algebraMap F L).range :=
  Polynomial.mem_range_of_eval_eq_const g x s hcard hval


-- created on 2026-10-20
