import sympy.core.mul
import sympy.Basic
open Tensor


@[main]
private lemma main
-- given
  (s out : List ℕ)
  (hlen : s.length = out.length)
  (i : ℕ) :
-- imply
  wrapFlat s out i = wrapFlat s out (i % out.prod) := by
-- proof
  induction s generalizing out i with
  | nil =>
    cases out with
    | nil =>
      simp [wrapFlat]
    | cons _ _ =>
      cases hlen
  | cons n s ih =>
    cases out with
    | nil =>
      cases hlen
    | cons k tout =>
      have hlen' : s.length = tout.length := by simpa using hlen
      simp only [wrapFlat, List.prod_cons]
      have hdiv :
          (i % (k * tout.prod)) / tout.prod = i / tout.prod % k :=
        Nat.mod_mul_left_div_self i tout.prod k
      have htail := ih tout hlen' i
      have htail' := ih tout hlen' (i % (k * tout.prod))
      have hmod : (i % (k * tout.prod)) % tout.prod = i % tout.prod :=
        Nat.mod_mod_of_dvd i (Nat.dvd_mul_left tout.prod k)
      rw [htail, htail', hmod, hdiv, Nat.mod_mod]


-- created on 2026-10-07
