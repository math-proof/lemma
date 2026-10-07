import Mathlib
import sympy.Basic


/--
[IharaTower_RungAssembly_map_delta_of_sq_sub](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaTower_RungAssembly_map_delta_of_sq_sub.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [CommRing T] [Algebra 𝒪 T]
  {πT : T →ₐ[𝒪] 𝒪}
  {a t Δ : T}
  {p nu nl nq n1 : ℕ}
-- given
  (hnu : nu = 1)
  (hnl : nl = 1)
  (hnq : nq = p + 1)
  (hn1 : n1 = p + 1)
  (hαq : a * a - t * a + algebraMap 𝒪 T (p : 𝒪) = 0)
  (hΔ : Δ = a ^ 2 * (algebraMap 𝒪 T (nu : 𝒪) * t) - a * (algebraMap 𝒪 T (nq : 𝒪) + algebraMap 𝒪 T (n1 : 𝒪)) + algebraMap 𝒪 T (nl : 𝒪) * t) :
-- imply
  πT Δ = (πT a - πT (t - a)) * (πT a ^ 2 - 1) := by
-- proof
  subst hnu hnl hnq hn1 hΔ
  have hab : πT a * πT (t - a) = p := by
    have h := congrArg πT hαq
    simp only [map_add, map_sub, map_mul, map_natCast, map_zero] at h
    rw [map_sub]
    linear_combination -h
  simp only [map_sub, map_mul, map_add, map_pow, map_natCast, Nat.cast_one, Nat.cast_add, map_one] at hab ⊢
  linear_combination (2 * πT a) * hab


-- created on 2026-10-05
