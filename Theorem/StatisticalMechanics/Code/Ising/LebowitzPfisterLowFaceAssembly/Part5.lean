/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterFourBridgeEndpointZero
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceCertificate
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly.Part5
open Finset


namespace StatMech.Ising

open StatMech.FrontierA

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace LowFaceCertificate

lemma evalTerms_radialFlatMap (ts : List TriTerm) (r q h : Real) :
    evalTerms (ts.flatMap fun t =>
      let degree := t.ex + t.ey + t.ez
      (TriPoly.const t.coeff * vx ^ t.ex * vy ^ (t.ex + t.ey) *
        vz ^ (degree - 3) * (1 + vy + vx * vy) ^ (6 - degree)).terms) r q h =
      radialEvalTerms ts r q h := by
  induction ts with
  | nil => simp [radialEvalTerms, evalTerms]
  | cons t ts ih =>
      rw [List.flatMap_cons, evalTerms_append, ih]
      change (TriPoly.const t.coeff * vx ^ t.ex * vy ^ (t.ex + t.ey) *
          vz ^ (t.ex + t.ey + t.ez - 3) *
          (1 + vy + vx * vy) ^ (6 - (t.ex + t.ey + t.ez))).eval r q h +
        radialEvalTerms ts r q h = radialEvalTerms (t :: ts) r q h
      simp only [eval_mul, eval_pow, eval_add, eval_const, eval_one]
      norm_num [vx, vy, vz, TriPoly.eval, evalTerms, TriTerm.eval]
      simp only [radialEvalTerms, radialTermEval]

lemma eval_radialize (p : TriPoly) (r q h : Real) :
    (radialize p).eval r q h = radialEvalTerms p.terms r q h := by
  rw [radialize, eval_ofTerms, evalTerms_radialFlatMap]

lemma radialTermEval_relation (t : TriTerm) (r q z : Real)
    (hlo : 3 <= t.ex + t.ey + t.ez)
    (hhi : t.ex + t.ey + t.ez <= 6) :
    z ^ 3 * radialTermEval t r q (z * (1 + q + r * q)) =
      (1 + q + r * q) ^ 3 * t.eval (r * q * z) (q * z) z := by
  let d := t.ex + t.ey + t.ez
  have hd0 : 3 + (d - 3) = d := by omega
  have hd1 : (d - 3) + (6 - d) = 3 := by omega
  have hd2 : t.ex + t.ey + t.ez = d := rfl
  let D : Real := 1 + q + r * q
  have hzpow : z ^ 3 * z ^ (d - 3) = z ^ d := by
    rw [← pow_add, hd0]
  have hDpow : D ^ (d - 3) * D ^ (6 - d) = D ^ 3 := by
    rw [← pow_add, hd1]
  have hqpow : q ^ (t.ex + t.ey) = q ^ t.ex * q ^ t.ey := by rw [pow_add]
  have hzsplit : z ^ d = z ^ t.ex * z ^ t.ey * z ^ t.ez := by
    rw [← hd2, pow_add, pow_add]
  simp only [radialTermEval, TriTerm.eval]
  rw [show 1 + q + r * q = D by rfl, mul_pow]
  calc
    z ^ 3 *
        ((t.coeff : Real) * r ^ t.ex * q ^ (t.ex + t.ey) *
          (z ^ (d - 3) * D ^ (d - 3)) * D ^ (6 - d)) =
      (t.coeff : Real) * r ^ t.ex * q ^ (t.ex + t.ey) *
        (z ^ 3 * z ^ (d - 3)) * (D ^ (d - 3) * D ^ (6 - d)) := by ring
    _ = (t.coeff : Real) * r ^ t.ex * (q ^ t.ex * q ^ t.ey) *
        (z ^ t.ex * z ^ t.ey * z ^ t.ez) * D ^ 3 := by
      rw [hzpow, hDpow, hqpow, hzsplit]
    _ = D ^ 3 *
        ((t.coeff : Real) * (r ^ t.ex * q ^ t.ex * z ^ t.ex) *
          (q ^ t.ey * z ^ t.ey) * z ^ t.ez) := by ring
    _ = D ^ 3 *
        ((t.coeff : Real) * (r * q * z) ^ t.ex *
          (q * z) ^ t.ey * z ^ t.ez) := by
      simp only [mul_pow]

lemma radialEvalTerms_relation (ts : List TriTerm) (r q z : Real)
    (hbounds : ∀ t ∈ ts,
      3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6) :
    z ^ 3 * radialEvalTerms ts r q (z * (1 + q + r * q)) =
      (1 + q + r * q) ^ 3 * evalTerms ts (r * q * z) (q * z) z := by
  induction ts with
  | nil => simp [radialEvalTerms, evalTerms]
  | cons t ts ih =>
      have ht := hbounds t (by simp)
      have hts : ∀ s ∈ ts,
          3 <= s.ex + s.ey + s.ez ∧ s.ex + s.ey + s.ez <= 6 := by
        intro s hs
        exact hbounds s (by simp [hs])
      rw [radialEvalTerms, evalTerms]
      calc
        z ^ 3 *
            (radialTermEval t r q (z * (1 + q + r * q)) +
              radialEvalTerms ts r q (z * (1 + q + r * q))) =
          z ^ 3 * radialTermEval t r q (z * (1 + q + r * q)) +
            z ^ 3 * radialEvalTerms ts r q (z * (1 + q + r * q)) := by ring
        _ = (1 + q + r * q) ^ 3 * t.eval (r * q * z) (q * z) z +
            (1 + q + r * q) ^ 3 * evalTerms ts (r * q * z) (q * z) z := by
          rw [radialTermEval_relation t r q z ht.1 ht.2, ih hts]
        _ = (1 + q + r * q) ^ 3 *
            (t.eval (r * q * z) (q * z) z +
              evalTerms ts (r * q * z) (q * z) z) := by ring

lemma eval_radialize_relation (p : TriPoly) (r q z : Real)
    (hbounds : ∀ t ∈ p.terms,
      3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6) :
    z ^ 3 * (radialize p).eval r q (z * (1 + q + r * q)) =
      (1 + q + r * q) ^ 3 * p.eval (r * q * z) (q * z) z := by
  rw [eval_radialize, radialEvalTerms_relation p.terms r q z hbounds]
  simp only [TriPoly.eval]


lemma TriPoly.eval_nonneg_of_radialize_relation
    (p : TriPoly) (r q z : Real)
    (hz : 0 <= z)
    (hD : 0 < 1 + q + r * q)
    (hbounds : ∀ t ∈ p.terms,
      3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6)
    (hrad : 0 <= (radialize p).eval r q (z * (1 + q + r * q))) :
    0 <= p.eval (r * q * z) (q * z) z := by
  have hleft : 0 <= z ^ 3 *
      (radialize p).eval r q (z * (1 + q + r * q)) :=
    mul_nonneg (pow_nonneg hz 3) hrad
  rw [eval_radialize_relation p r q z hbounds] at hleft
  exact nonneg_of_mul_nonneg_right hleft (pow_pos hD 3)

end LowFaceCertificate
end
end StatMech.Ising
