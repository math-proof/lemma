/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Ramanujan/Part1Ch9Entry26Ramanujanpi.lean -/


import sympy.atlas.Analysis.Ramanujan.Part1Ch9Entry26Ramanujanpi
import Lemma.Real.Ramanujan.Part1Ch9Entry26Ramanujanpi

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi

open Complex

example : chapter9BoundaryLog 0 = Real.log 0 :=
  chapter9BoundaryLog_eq_log 0

example :
    chapter9DilogCosTerm (1 / 2) (Real.pi / 3) 2 =
      Entry24Dougall.chapter9DilogCosTerm (1 / 2) (Real.pi / 3) 2 :=
  chapter9DilogCosTerm_eq_entry24 (1 / 2) (Real.pi / 3) 2

example :
    chapter9DilogSinTerm (2 / 3) (-Real.pi / 5) 4 =
      Entry24Dougall.chapter9DilogSinTerm (2 / 3) (-Real.pi / 5) 4 :=
  chapter9DilogSinTerm_eq_entry24 (2 / 3) (-Real.pi / 5) 4

example (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * exp (I * (theta : ℂ)) +
          (y : ℂ) * exp (I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) * exp (I * ((theta + phi : ℝ) : ℂ)) = 1) :
    Summable (fun j : ℕ => Entry24Dougall.chapter9DilogCosTerm x theta (2 * j)) :=
  (ramanujan_part1_ch9_entry26_ramanujanpi_entry24_terms x y theta phi hx0 hx1 hy0 hy1
    htheta0 htheta1 hphi0 hphi1 hrelation).1

-- The public theorem supplies the cosine-series summability conclusion from local hypotheses.
example (x y theta phi : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1)
    (htheta0 : -Real.pi < theta) (htheta1 : theta ≤ Real.pi)
    (hphi0 : -Real.pi < phi) (hphi1 : phi ≤ Real.pi)
    (hrelation :
      (x : ℂ) * exp (I * (theta : ℂ)) +
          (y : ℂ) * exp (I * (phi : ℂ)) +
          ((x * y : ℝ) : ℂ) * exp (I * ((theta + phi : ℝ) : ℂ)) = 1) :
    Summable (fun j : ℕ => chapter9DilogCosTerm x theta (2 * j)) :=
  (ramanujan_part1_ch9_entry26_ramanujanpi x y theta phi hx0 hx1 hy0 hy1
    htheta0 htheta1 hphi0 hphi1 hrelation).1

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry26Ramanujanpi
