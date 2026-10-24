import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterLowFaceAssembly
open Finset StatMech StatMech.Ising StatMech.Ising.LowFaceCertificate


/--
[evalTerms_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_insert_eq
  [Fintype V]
  [DecidableEq V]
  {t : TriTerm}
  {ts : List TriTerm}
  {x y z : Real} :
-- imply
  evalTerms (TriPoly.insert t ts) x y z = t.eval x y z + evalTerms ts x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_insert t ts x y z

/--
[evalTerms_foldl_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_foldl_insert_eq
  [Fintype V]
  [DecidableEq V]
  {out ts : List TriTerm}
  {x y z : Real} :
-- imply
  evalTerms (ts.foldl (fun acc t => TriPoly.insert t acc) out) x y z = evalTerms out x y z + evalTerms ts x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_foldl_insert out ts x y z

/--
[eval_ofTerms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_ofTerms_eq
  [Fintype V]
  [DecidableEq V]
  {ts : List TriTerm}
  {x y z : Real} :
-- imply
  (TriPoly.ofTerms ts).eval x y z = evalTerms ts x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_ofTerms ts x y z

/--
[eval_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_const_eq
  [Fintype V]
  [DecidableEq V]
  {q : Int}
  {x y z : Real} :
-- imply
  (TriPoly.const q).eval x y z = q := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_const q x y z

/--
[evalTerms_negMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_negMap_eq
  [Fintype V]
  [DecidableEq V]
  {ts : List TriTerm}
  {x y z : Real} :
-- imply
  evalTerms (ts.map fun t => { t with coeff := -t.coeff }) x y z = -evalTerms ts x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_negMap ts x y z

/--
[eval_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_neg_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
  {x y z : Real} :
-- imply
  (-p).eval x y z = -p.eval x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_neg p x y z

/--
[evalTerms_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_append_eq
  [Fintype V]
  [DecidableEq V]
  {ps qs : List TriTerm}
  {x y z : Real} :
-- imply
  evalTerms (ps ++ qs) x y z = evalTerms ps x y z + evalTerms qs x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_append ps qs x y z

/--
[eval_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_add_eq
  [Fintype V]
  [DecidableEq V]
  {p q : TriPoly}
  {x y z : Real} :
-- imply
  (p + q).eval x y z = p.eval x y z + q.eval x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_add p q x y z

/--
[eval_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_sub_eq
  [Fintype V]
  [DecidableEq V]
  {p q : TriPoly}
  {x y z : Real} :
-- imply
  (p - q).eval x y z = p.eval x y z - q.eval x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_sub p q x y z

/--
[eval_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_zero_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (0 : TriPoly).eval x y z = 0 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_zero x y z

/--
[eval_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_one_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (1 : TriPoly).eval x y z = 1 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_one x y z

/--
[eval_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_two_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (2 : TriPoly).eval x y z = 2 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_two x y z

/--
[eval_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_three_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (3 : TriPoly).eval x y z = 3 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_three x y z

/--
[eval_six](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_six_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (6 : TriPoly).eval x y z = 6 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_six x y z

/--
[eval_nine](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_nine_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (9 : TriPoly).eval x y z = 9 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_nine x y z

/--
[eval_1764](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_1764_eq
  [Fintype V]
  [DecidableEq V]
  {x y z : Real} :
-- imply
  (1764 : TriPoly).eval x y z = 1764 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_1764 x y z

/--
[evalTerms_mulMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_mulMap_eq
  [Fintype V]
  [DecidableEq V]
  {s : TriTerm}
  {ts : List TriTerm}
  {x y z : Real} :
-- imply
  evalTerms (ts.map fun t => { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez, coeff := s.coeff * t.coeff }) x y z = s.eval x y z * evalTerms ts x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_mulMap s ts x y z

/--
[evalTerms_mulFlatMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_mulFlatMap_eq
  [Fintype V]
  [DecidableEq V]
  {ss ts : List TriTerm}
  {x y z : Real} :
-- imply
  evalTerms (ss.flatMap fun s => ts.map fun t => { ex := s.ex + t.ex, ey := s.ey + t.ey, ez := s.ez + t.ez, coeff := s.coeff * t.coeff }) x y z = evalTerms ss x y z * evalTerms ts x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_mulFlatMap ss ts x y z

/--
[eval_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_mul_eq
  [Fintype V]
  [DecidableEq V]
  {p q : TriPoly}
  {x y z : Real} :
-- imply
  (p * q).eval x y z = p.eval x y z * q.eval x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_mul p q x y z

/--
[eval_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_pow_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
  {n : Nat}
  {x y z : Real} :
-- imply
  (p ^ n).eval x y z = p.eval x y z ^ n := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_pow p n x y z

/--
[bernsteinWeight_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinWeight_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {n i : Nat}
  {x : Real}
-- given
  (hx0 : 0 <= x)
  (hx1 : x <= 1) :
-- imply
  0 <= bernsteinWeight n i x := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinWeight_nonneg hx0 hx1

/--
[scaledBernFactor_sum_twelve](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma scaledBernFactor_sum_twelve_eq
  [Fintype V]
  [DecidableEq V]
  {e : Nat}
  {x : Real}
-- given
  (he : e <= 6) :
-- imply
  ∑ i : Fin 13, (scaledBernFactor 12 27720 e i : Real) * bernsteinWeight 12 i x = 27720 * x ^ e := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.scaledBernFactor_sum_twelve e he x

/--
[scaledBernFactor_sum_seven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma scaledBernFactor_sum_seven_eq
  [Fintype V]
  [DecidableEq V]
  {e : Nat}
  {x : Real}
-- given
  (he : e <= 6) :
-- imply
  ∑ i : Fin 8, (scaledBernFactor 7 105 e i : Real) * bernsteinWeight 7 i x = 105 * x ^ e := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.scaledBernFactor_sum_seven e he x

/--
[scaledBernFactor_sum_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma scaledBernFactor_sum_three_eq
  [Fintype V]
  [DecidableEq V]
  {e : Nat}
  {x : Real}
-- given
  (he : e <= 3) :
-- imply
  ∑ i : Fin 4, (scaledBernFactor 3 3 e i : Real) * bernsteinWeight 3 i x = 3 * x ^ e := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.scaledBernFactor_sum_three e he x

/--
[foldl_radialTermCoeff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma foldl_radialTermCoeff_eq
  [Fintype V]
  [DecidableEq V]
  {ts : List TriTerm}
  {q : Int}
  {a : Fin 13}
  {b : Fin 8}
  {c : Fin 4} :
-- imply
  ts.foldl (fun q t => q + radialTermCoeff t a b c) q = q + radialCoeffTerms ts a b c := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.foldl_radialTermCoeff ts q a b c

/--
[radialBernCoeffOf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma radialBernCoeffOf_eq_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
  {a : Fin 13}
  {b : Fin 8}
  {c : Fin 4} :
-- imply
  radialBernCoeffOf p a b c = radialCoeffTerms p.terms a b c := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radialBernCoeffOf_eq p a b c

/--
[radialTerm_bernstein_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma radialTerm_bernstein_sum_eq
  [Fintype V]
  [DecidableEq V]
  {t : TriTerm}
-- given
  (r q h : Real)
  (hex : t.ex <= 6)
  (hey : t.ey <= 6)
  (hez : t.ez <= 3) :
-- imply
  (∑ a : Fin 13, ∑ b : Fin 8, ∑ c : Fin 4, (radialTermCoeff t a b c : Real) * bernsteinWeight 12 a r * bernsteinWeight 7 b q * bernsteinWeight 3 c h) = (27720 * 105 * 3 : Real) * t.eval r q h := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radialTerm_bernstein_sum t r q h hex hey hez

/--
[bernsteinEvalTerms_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinEvalTerms_eq_eq
  [Fintype V]
  [DecidableEq V]
  {ts : List TriTerm}
-- given
  (r q h : Real)
  (hbounds : ∀ t ∈ ts, t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3) :
-- imply
  bernsteinEvalTerms ts r q h = (27720 * 105 * 3 : Real) * evalTerms ts r q h := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinEvalTerms_eq ts r q h hbounds

/--
[TriPoly.eval_nonneg_of_bernstein](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_nonneg_of_bernstein_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
-- given
  (r q h : Real)
  (hr0 : 0 <= r)
  (hr1 : r <= 1)
  (hq0 : 0 <= q)
  (hq1 : q <= 1)
  (hh0 : 0 <= h)
  (hh1 : h <= 1)
  (hbounds : ∀ t ∈ p.terms, t.ex <= 6 ∧ t.ey <= 6 ∧ t.ez <= 3)
  (hcoeff : ∀ (a : Fin 13) (b : Fin 8) (c : Fin 4), 0 <= radialBernCoeffOf p a b c) :
-- imply
  0 <= p.eval r q h := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.TriPoly.eval_nonneg_of_bernstein p r q h hr0 hr1 hq0 hq1 hh0 hh1 hbounds hcoeff

/--
[radializedCrossCoeff_eval_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma radializedCrossCoeff_eval_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : Fin 8}
-- given
  (r q h : Real)
  (hr0 : 0 <= r)
  (hr1 : r <= 1)
  (hq0 : 0 <= q)
  (hq1 : q <= 1)
  (hh0 : 0 <= h)
  (hh1 : h <= 1) :
-- imply
  0 <= (radialize (crossCoeffPoly i j k)).eval r q h := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radializedCrossCoeff_eval_nonneg i j k r q h hr0 hr1 hq0 hq1 hh0 hh1

/--
[evalTerms_radialFlatMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma evalTerms_radialFlatMap_eq
  [Fintype V]
  [DecidableEq V]
  {ts : List TriTerm}
-- given
  (r q h : Real) :
-- imply
  evalTerms (ts.flatMap fun t => let degree := t.ex + t.ey + t.ez (TriPoly.const t.coeff * vx ^ t.ex * vy ^ (t.ex + t.ey) * vz ^ (degree - 3) * (1 + vy + vx * vy) ^ (6 - degree)).terms) r q h = radialEvalTerms ts r q h := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.evalTerms_radialFlatMap ts r q h

/--
[eval_radialize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_radialize_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
-- given
  (r q h : Real) :
-- imply
  (radialize p).eval r q h = radialEvalTerms p.terms r q h := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_radialize p r q h

/--
[radialTermEval_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma radialTermEval_relation_eq
  [Fintype V]
  [DecidableEq V]
  {t : TriTerm}
  {r q z : Real}
-- given
  (hlo : 3 <= t.ex + t.ey + t.ez)
  (hhi : t.ex + t.ey + t.ez <= 6) :
-- imply
  z ^ 3 * radialTermEval t r q (z * (1 + q + r * q)) = (1 + q + r * q) ^ 3 * t.eval (r * q * z) (q * z) z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radialTermEval_relation t r q z hlo hhi

/--
[radialEvalTerms_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma radialEvalTerms_relation_eq
  [Fintype V]
  [DecidableEq V]
  {ts : List TriTerm}
  {r q z : Real}
-- given
  (hbounds : ∀ t ∈ ts, 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6) :
-- imply
  z ^ 3 * radialEvalTerms ts r q (z * (1 + q + r * q)) = (1 + q + r * q) ^ 3 * evalTerms ts (r * q * z) (q * z) z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.radialEvalTerms_relation ts r q z hbounds

/--
[eval_radialize_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_radialize_relation_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
  {r q z : Real}
-- given
  (hbounds : ∀ t ∈ p.terms, 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6) :
-- imply
  z ^ 3 * (radialize p).eval r q (z * (1 + q + r * q)) = (1 + q + r * q) ^ 3 * p.eval (r * q * z) (q * z) z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_radialize_relation p r q z hbounds

/--
[TriPoly.eval_nonneg_of_radialize_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_nonneg_of_radialize_relation_eq
  [Fintype V]
  [DecidableEq V]
  {p : TriPoly}
  {r q z : Real}
-- given
  (hz : 0 <= z)
  (hD : 0 < 1 + q + r * q)
  (hbounds : ∀ t ∈ p.terms, 3 <= t.ex + t.ey + t.ez ∧ t.ex + t.ey + t.ez <= 6)
  (hrad : 0 <= (radialize p).eval r q (z * (1 + q + r * q))) :
-- imply
  0 <= p.eval (r * q * z) (q * z) z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.TriPoly.eval_nonneg_of_radialize_relation p r q z hz hD hbounds hrad

/--
[eval_crossCoeffPoly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma eval_crossCoeffPoly_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : Nat}
  {x y z : Real} :
-- imply
  (crossCoeffPoly i j k).eval x y z = 1764 * y * z * (x - x ^ 3 + y - y ^ 3 + z - z ^ 3) + (252 * i : Int) * (9 * x * y * z * (x + y) * (1 - y)) + (252 * j : Int) * (9 * x * y * z * (x + z) * (1 - z)) + (252 * k : Int) * (9 * y ^ 2 * z * (y + z) * (1 - z)) - (36 * i * j : Int) * (3 * x * y * z * (3 - 2 * x) * (1 - y) * (1 - z)) + (6 * i * (i - 1) * j : Int) * (6 * x ^ 2 * z * (1 - y) ^ 2 * (1 - z)) + (6 * j * (j - 1) * i : Int) * (6 * x ^ 2 * y * (1 - y) * (1 - z) ^ 2) - (36 * i * k : Int) * (3 * x * y * z * (3 - 2 * y) * (1 - y) * (1 - z)) + (6 * i * (i - 1) * k : Int) * (6 * x * y * z * (1 - y) ^ 2 * (1 - z)) + (6 * k * (k - 1) * i : Int) * (6 * x * y ^ 2 * (1 - y) * (1 - z) ^ 2) - (36 * j * k : Int) * (3 * x * y ^ 2 * (3 - 2 * z) * (1 - z) ^ 2) + (6 * j * (j - 1) * k : Int) * (6 * x * y ^ 2 * (1 - z) ^ 3) + (6 * k * (k - 1) * j : Int) * (6 * x * y ^ 2 * (1 - z) ^ 3) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.eval_crossCoeffPoly i j k x y z

/--
[bernsteinAverageSeven_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinAverageSeven_const_eq
  [Fintype V]
  [DecidableEq V]
  {x q : Real} :
-- imply
  bernsteinAverageSeven x (fun _ => q) = q := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinAverageSeven_const x q

/--
[bernsteinAverageSeven_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinAverageSeven_add_eq
  [Fintype V]
  [DecidableEq V]
  {x : Real}
-- given
  (f g : Fin 8 -> Real) :
-- imply
  bernsteinAverageSeven x (fun i => f i + g i) = bernsteinAverageSeven x f + bernsteinAverageSeven x g := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinAverageSeven_add x f g

/--
[bernsteinAverageSeven_natCast_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinAverageSeven_natCast_mul_eq
  [Fintype V]
  [DecidableEq V]
  {x q : Real} :
-- imply
  bernsteinAverageSeven x (fun i => q * i.val) = q * (7 * x) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinAverageSeven_natCast_mul x q

/--
[bernsteinAverageSeven_falling_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinAverageSeven_falling_mul_eq
  [Fintype V]
  [DecidableEq V]
  {x q : Real} :
-- imply
  bernsteinAverageSeven x (fun i => q * (i.val * (i.val - 1) : Nat)) = q * (42 * x ^ 2) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinAverageSeven_falling_mul x q

/--
[bernsteinAverageSeven_choose_two_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinAverageSeven_choose_two_mul_eq
  [Fintype V]
  [DecidableEq V]
  {x q : Real} :
-- imply
  bernsteinAverageSeven x (fun i => q * i.val.choose 2) = q * (21 * x ^ 2) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinAverageSeven_choose_two_mul x q

/--
[bernsteinAverageSeven_eq_quadraticAverage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma bernsteinAverageSeven_eq_quadraticAverage_eq
  [Fintype V]
  [DecidableEq V]
  {x : Real}
-- given
  (f : Fin 8 -> Real)
  (hquad : ∀ i : Fin 8, f i = f 0 + i.val * (f 1 - f 0) + i.val.choose 2 * (f 2 - 2 * f 1 + f 0)) :
-- imply
  bernsteinAverageSeven x f = quadraticAverage x f := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.bernsteinAverageSeven_eq_quadraticAverage x f hquad

/--
[quadraticAverage_preserves_quadratic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma quadraticAverage_preserves_quadratic_eq
  [Fintype V]
  [DecidableEq V]
  {x : Real}
  {i : Fin 8}
-- given
  (F : Fin 8 -> Fin 8 -> Real)
  (hquad : ∀ (i j : Fin 8), F i j = F 0 j + i.val * (F 1 j - F 0 j) + i.val.choose 2 * (F 2 j - 2 * F 1 j + F 0 j)) :
-- imply
  quadraticAverage x (fun j => F i j) = quadraticAverage x (fun j => F 0 j) + i.val * (quadraticAverage x (fun j => F 1 j) - quadraticAverage x (fun j => F 0 j)) + i.val.choose 2 * (quadraticAverage x (fun j => F 2 j) - 2 * quadraticAverage x (fun j => F 1 j) + quadraticAverage x (fun j => F 0 j)) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.quadraticAverage_preserves_quadratic x F hquad i

/--
[crossNumerator_bernstein_average](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma crossNumerator_bernstein_average_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real} :
-- imply
  bernsteinAverageSeven a (fun i => bernsteinAverageSeven b (fun j => bernsteinAverageSeven c (fun k => (crossCoeffPoly i j k).eval x y z))) = 1764 * crossNumerator x y z a b c := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossNumerator_bernstein_average x y z a b c

/--
[crossCoeffPoly_eval_nonneg_ordered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma crossCoeffPoly_eval_nonneg_ordered_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : Fin 8}
  {x y z : Real}
-- given
  (hx : 0 < x)
  (hxy : x <= y)
  (hyz : y <= z)
  (hsum : x + y + z <= 1) :
-- imply
  0 <= (crossCoeffPoly i j k).eval x y z := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossCoeffPoly_eval_nonneg_ordered i j k hx hxy hyz hsum

/--
[crossNumerator_nonneg_ordered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma crossNumerator_nonneg_ordered_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx : 0 < x)
  (hxy : x <= y)
  (hyz : y <= z)
  (hsum : x + y + z <= 1)
  (ha0 : 0 <= a)
  (ha1 : a <= 1)
  (hb0 : 0 <= b)
  (hb1 : b <= 1)
  (hc0 : 0 <= c)
  (hc1 : c <= 1) :
-- imply
  0 <= crossNumerator x y z a b c := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.crossNumerator_nonneg_ordered hx hxy hyz hsum ha0 ha1 hb0 hb1 hc0 hc1

/--
[fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx : 0 < x)
  (hxy : x <= y)
  (hyz : y <= z)
  (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hacap : y * a <= (1 - y ^ 2) * x)
  (hbcap : z * b <= (1 - z ^ 2) * x)
  (hccap : z * c <= (1 - z ^ 2) * y) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 6 * x * a * b * (x * y * z + y * b + z * a) + 6 * y * a * c * (x * y * z + x * c + z * a) + 6 * z * b * c * (x * y * z + x * c + y * b) - 9 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.fourBridge_triangle_cross_remainder_nonneg_ordered_of_caps hx hxy hyz hsum ha hb hc hacap hbcap hccap

/--
[fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx : 0 < x)
  (hy : 0 < y)
  (hz : 0 < z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
  (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
  (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 6 * x * a * b * (x * y * z + y * b + z * a) + 6 * y * a * c * (x * y * z + x * c + z * a) + 6 * z * b * c * (x * y * z + x * c + y * b) - 9 * (a * b * y * z + a * c * x * z + b * c * x * y) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.fourBridge_triangle_cross_remainder_nonneg_of_sqsum_le_one hx0 hy0 hz0 hx hy hz hx1 hy1 hz1 ha hb hc hxa hya hxb hzb hyc hzc hsum

/--
[fourBridge_triangle_correct_nonneg_of_sqsum_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma fourBridge_triangle_correct_nonneg_of_sqsum_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx : 0 < x)
  (hy : 0 < y)
  (hz : 0 < z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
  (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c)
  (hsum : x ^ 2 + y ^ 2 + z ^ 2 <= 1) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) + (-18 * a * b * y * z + 6 * x * a * b * (x * y * z + y * b + z * a)) + (-18 * a * c * x * z + 6 * y * a * c * (x * y * z + x * c + z * a)) + (-18 * b * c * x * y + 6 * z * b * c * (x * y * z + x * c + y * b)) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.fourBridge_triangle_correct_nonneg_of_sqsum_le_one hx0 hy0 hz0 hx hy hz hx1 hy1 hz1 ha hb hc hxa hya hxb hzb hyc hzc hsum

/--
[fourBridge_triangle_correct_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma fourBridge_triangle_correct_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {x y z a b c : Real}
-- given
  (hx0 : 0 <= x)
  (hy0 : 0 <= y)
  (hz0 : 0 <= z)
  (hx1 : x <= 1)
  (hy1 : y <= 1)
  (hz1 : z <= 1)
  (ha : 0 <= a)
  (hb : 0 <= b)
  (hc : 0 <= c)
  (hxa : x * a ^ 2 <= (1 - x ^ 2) * y * a)
  (hya : y * a ^ 2 <= (1 - y ^ 2) * x * a)
  (hxb : x * b ^ 2 <= (1 - x ^ 2) * z * b)
  (hzb : z * b ^ 2 <= (1 - z ^ 2) * x * b)
  (hyc : y * c ^ 2 <= (1 - y ^ 2) * z * c)
  (hzc : z * c ^ 2 <= (1 - z ^ 2) * y * c) :
-- imply
  0 <= x ^ 2 * (1 - x ^ 4) + y ^ 2 * (1 - y ^ 4) + z ^ 2 * (1 - z ^ 4) + 9 * (a * x * y * (x ^ 2 + y ^ 2) + b * x * z * (x ^ 2 + z ^ 2) + c * y * z * (y ^ 2 + z ^ 2)) + 9 / 2 * (a ^ 2 * (x ^ 2 + y ^ 2) + b ^ 2 * (x ^ 2 + z ^ 2) + c ^ 2 * (y ^ 2 + z ^ 2)) + (-18 * a * b * y * z + 6 * x * a * b * (x * y * z + y * b + z * a)) + (-18 * a * c * x * z + 6 * y * a * c * (x * y * z + x * c + z * a)) + (-18 * b * c * x * y + 6 * z * b * c * (x * y * z + x * c + y * b)) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.fourBridge_triangle_correct_nonneg hx0 hy0 hz0 hx1 hy1 hz1 ha hb hc hxa hya hxb hzb hyc hzc

/--
[fourBridge_Ursell_correction_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma fourBridge_Ursell_correction_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {m0 m1 m2 m3 c01 c02 c03 c12 c13 c23 : Real}
-- given
  (hm00 : 0 <= m0)
  (hm10 : 0 <= m1)
  (hm20 : 0 <= m2)
  (hm30 : 0 <= m3)
  (hm01 : m0 <= 1)
  (hm11 : m1 <= 1)
  (hm21 : m2 <= 1)
  (hm31 : m3 <= 1)
  (hc01 : 0 <= c01)
  (hc02 : 0 <= c02)
  (hc03 : 0 <= c03)
  (hc12 : 0 <= c12)
  (hc13 : 0 <= c13)
  (hc23 : 0 <= c23)
  (h001 : m0 * c01 ^ 2 <= (1 - m0 ^ 2) * m1 * c01)
  (h101 : m1 * c01 ^ 2 <= (1 - m1 ^ 2) * m0 * c01)
  (h002 : m0 * c02 ^ 2 <= (1 - m0 ^ 2) * m2 * c02)
  (h202 : m2 * c02 ^ 2 <= (1 - m2 ^ 2) * m0 * c02)
  (h003 : m0 * c03 ^ 2 <= (1 - m0 ^ 2) * m3 * c03)
  (h303 : m3 * c03 ^ 2 <= (1 - m3 ^ 2) * m0 * c03)
  (h112 : m1 * c12 ^ 2 <= (1 - m1 ^ 2) * m2 * c12)
  (h212 : m2 * c12 ^ 2 <= (1 - m2 ^ 2) * m1 * c12)
  (h113 : m1 * c13 ^ 2 <= (1 - m1 ^ 2) * m3 * c13)
  (h313 : m3 * c13 ^ 2 <= (1 - m3 ^ 2) * m1 * c13)
  (h223 : m2 * c23 ^ 2 <= (1 - m2 ^ 2) * m3 * c23)
  (h323 : m3 * c23 ^ 2 <= (1 - m3 ^ 2) * m2 * c23) :
-- imply
  let p01 := m0 * m1 + c01 let p02 := m0 * m2 + c02 let p03 := m0 * m3 + c03 let p12 := m1 * m2 + c12 let p13 := m1 * m3 + c13 let p23 := m2 * m3 + c23 let u012 := m0 * p12 + m1 * p02 + m2 * p01 - 2 * m0 * m1 * m2 let u013 := m0 * p13 + m1 * p03 + m3 * p01 - 2 * m0 * m1 * m3 let u023 := m0 * p23 + m2 * p03 + m3 * p02 - 2 * m0 * m2 * m3 let u123 := m1 * p23 + m2 * p13 + m3 * p12 - 2 * m1 * m2 * m3 let aa := m0 ^ 2 + m1 ^ 2 + m2 ^ 2 + m3 ^ 2 let bb := p01 ^ 2 + p02 ^ 2 + p03 ^ 2 + p12 ^ 2 + p13 ^ 2 + p23 ^ 2 0 <= aa + 3 * aa * bb - aa ^ 3 - 3 * (u012 ^ 2 + u013 ^ 2 + u023 ^ 2 + u123 ^ 2) + 2 * (m0 * c01 * c02 * (m0 * m1 * m2 + m1 * c02 + m2 * c01) + m1 * c01 * c12 * (m0 * m1 * m2 + m0 * c12 + m2 * c01) + m2 * c02 * c12 * (m0 * m1 * m2 + m0 * c12 + m1 * c02)) + 2 * (m0 * c01 * c03 * (m0 * m1 * m3 + m1 * c03 + m3 * c01) + m1 * c01 * c13 * (m0 * m1 * m3 + m0 * c13 + m3 * c01) + m3 * c03 * c13 * (m0 * m1 * m3 + m0 * c13 + m1 * c03)) + 2 * (m0 * c02 * c03 * (m0 * m2 * m3 + m2 * c03 + m3 * c02) + m2 * c02 * c23 * (m0 * m2 * m3 + m0 * c23 + m3 * c02) + m3 * c03 * c23 * (m0 * m2 * m3 + m0 * c23 + m2 * c03)) + 2 * (m1 * c12 * c13 * (m1 * m2 * m3 + m2 * c13 + m3 * c12) + m2 * c12 * c23 * (m1 * m2 * m3 + m1 * c23 + m3 * c12) + m3 * c13 * c23 * (m1 * m2 * m3 + m1 * c23 + m2 * c13)) := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.fourBridge_Ursell_correction_nonneg hm00 hm10 hm20 hm30 hm01 hm11 hm21 hm31 hc01 hc02 hc03 hc12 hc13 hc23 h001 h101 h002 h202 h003 h303 h112 h212 h113 h313 h223 h323

/--
[fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterLowFaceAssembly.lean)
-/
@[path]
private lemma fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {w x y z : V}
-- given
  (K : Sym2 V -> Real)
  (hf : V -> Real)
  (hK : forall e, 0 <= K e)
  (hhf : forall v, 0 <= hf v)
  (hwx : w ≠ x)
  (hwy : w ≠ y)
  (hwz : w ≠ z)
  (hxy : x ≠ y)
  (hxz : x ≠ z)
  (hyz : y ≠ z) :
-- imply
  fourBridgeVarianceSkewBernsteinCoeff (fourBridgeOneCoeff G K hf w x y z) (fourBridgeTwoCoeff G K hf w x y z) (fourBridgeThreeCoeff G K hf w x y z) (fourBridgeFourCoeff G K hf w x y z) 0 <= 0 := by
-- proof
  apply StatMech.Ising.LowFaceCertificate.fourBridgeVarianceSkewBernsteinCoeff_zero_nonpos G K hf hK hhf hwx hwy hwz hxy hxz hyz


-- created on 2026-10-23
