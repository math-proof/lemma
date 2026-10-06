import Mathlib
import sympy.Basic


/--
[WeierstrassCurve_map_frobenius_dualNumber_eq_map_map_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_WeierstrassCurve_map_frobenius_dualNumber_eq_map_map_map.lean)
-/
@[main]
private lemma main
  [Field k]
  {q : ℕ} [Fact q.Prime] [CharP k q] [CharP (DualNumber k) q]
  {W : WeierstrassCurve (DualNumber k)} :
-- imply
  W.map (frobenius (DualNumber k) q) =
      ((W.map (TrivSqZeroExt.fstHom k k k).toRingHom).map (frobenius k q)).map (algebraMap k (DualNumber k)) := by
-- proof
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have key : frobenius (DualNumber k) q =
      (algebraMap k (DualNumber k)).comp ((frobenius k q).comp (TrivSqZeroExt.fstHom k k k).toRingHom) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply, frobenius_def]
    have hx : x = algebraMap k (DualNumber k) x.fst + TrivSqZeroExt.inr x.snd := by
      rw [TrivSqZeroExt.algebraMap_eq_inl]; exact (TrivSqZeroExt.inl_fst_add_inr_snd_eq x).symm
    have hn : (TrivSqZeroExt.inr x.snd : DualNumber k) ^ q = 0 := by
      rw [← Nat.sub_add_cancel hq2, pow_add, pow_two, TrivSqZeroExt.inr_mul_inr, mul_zero]
    conv_lhs => rw [hx, add_pow_char, ← map_pow, hn, add_zero]
    rfl
  simp only [WeierstrassCurve.map_map]
  rw [key]


-- created on 2026-10-05
