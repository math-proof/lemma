import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[RatFunc_trdeg_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RatFunc_trdeg_eq_one.lean)
-/

private lemma isAlgebraic_adjoin_X
  (K : Type u)
  [Field K] :
  Algebra.IsAlgebraic (Algebra.adjoin K ({(RatFunc.X : RatFunc K)} : Set (RatFunc K))) (RatFunc K) := by
  classical
  set A := Algebra.adjoin K ({(RatFunc.X : RatFunc K)} : Set (RatFunc K)) with hA
  have hmem : ∀ q : K[X], algebraMap K[X] (RatFunc K) q ∈ A := by
    intro q
    have : algebraMap K[X] (RatFunc K) q = Polynomial.aeval (RatFunc.X : RatFunc K) q := by
      rw [RatFunc.aeval_X_left_eq_algebraMap]
    rw [this, hA, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨q, rfl⟩
  refine ⟨fun f => ?_⟩
  let d : A := ⟨algebraMap K[X] (RatFunc K) f.denom, hmem _⟩
  let n : A := ⟨algebraMap K[X] (RatFunc K) f.num, hmem _⟩
  have hd : (d : RatFunc K) ≠ 0 := by
    simp only [d, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))]
    exact RatFunc.denom_ne_zero f
  have hd' : d ≠ 0 := fun h => hd (by rw [h]; rfl)
  refine ⟨Polynomial.C d * Polynomial.X - Polynomial.C n, ?_, ?_⟩
  ·
    intro h
    have := congrArg (fun P => P.coeff 1) h
    simp [Polynomial.coeff_C, hd'] at this
  ·
    rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
    change (d : RatFunc K) * f - (n : RatFunc K) = 0
    rw [sub_eq_zero, mul_comm]
    exact ((div_eq_iff hd).mp (RatFunc.num_div_denom f)).symm

private lemma trdeg_ratFunc_eq_one
  (K : Type u)
  [Field K]
  : Algebra.trdeg K (RatFunc K) = 1 := by
  apply le_antisymm
  ·
    have := isAlgebraic_adjoin_X K
    have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk K ({(RatFunc.X : RatFunc K)} : Set (RatFunc K))
    simpa using h
  · exact Cardinal.one_le_iff_pos.mpr (trdeg_pos (R := K) (A := RatFunc K))


universe u
@[path]
private lemma main
  {K : Type u} [Field K] :
-- imply
  Algebra.trdeg K (RatFunc K) = 1 :=
-- proof
  trdeg_ratFunc_eq_one K


-- created on 2026-10-23
