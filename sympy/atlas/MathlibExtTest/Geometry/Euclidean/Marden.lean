/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Geometry/Euclidean/Marden.lean -/


import Lemma.Set.Euclidean.Marden

namespace MetaMathlibExt

-- The theorem gives strict tangency on the horizontal side of the triangle `0, 1, I`.
example (f1 f2 : ℂ)
    (hroots : Polynomial.roots (Polynomial.derivative
      ((Polynomial.X - Polynomial.C 0) *
        (Polynomial.X - Polynomial.C 1) *
        (Polynomial.X - Polynomial.C Complex.I))) = {f1, f2})
    (t : ℝ) (ht : t ≠ 0) :
    ‖(1 : ℂ) / 2 - f1‖ + ‖(1 : ℂ) / 2 - f2‖ <
      ‖(1 : ℂ) / 2 + (t : ℂ) - f1‖ + ‖(1 : ℂ) / 2 + (t : ℂ) - f2‖ := by
  have hnondeg : (((1 : ℂ) - 0) / (Complex.I - 0)).im ≠ 0 := by norm_num
  rcases marden 0 1 Complex.I hnondeg with
    ⟨g1, g2, L, hgroots, hgmid, _, _, hgstrict, _, _⟩
  have hpairs : ({f1, f2} : Multiset ℂ) = {g1, g2} := hroots.symm.trans hgroots
  have hdist (z : ℂ) :
      ‖z - f1‖ + ‖z - f2‖ = ‖z - g1‖ + ‖z - g2‖ := by
    have hmap := congrArg
      (fun s : Multiset ℂ => (s.map fun f => ‖z - f‖).sum) hpairs
    simpa using hmap
  calc
    ‖(1 : ℂ) / 2 - f1‖ + ‖(1 : ℂ) / 2 - f2‖ =
        ‖(1 : ℂ) / 2 - g1‖ + ‖(1 : ℂ) / 2 - g2‖ := hdist _
    _ = L := by simpa using hgmid
    _ < ‖(1 : ℂ) / 2 + (t : ℂ) - g1‖ +
        ‖(1 : ℂ) / 2 + (t : ℂ) - g2‖ := by simpa using hgstrict t ht
    _ = ‖(1 : ℂ) / 2 + (t : ℂ) - f1‖ +
        ‖(1 : ℂ) / 2 + (t : ℂ) - f2‖ := (hdist _).symm

end MetaMathlibExt
