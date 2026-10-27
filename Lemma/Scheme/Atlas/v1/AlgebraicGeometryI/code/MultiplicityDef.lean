import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.MultiplicityDef
open MvPolynomial


namespace MvPolynomial

/--
[translate_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean)
-/
@[path]
lemma translate_def
  [CommRing k]
  {p : σ → k}
  {f : MvPolynomial σ k} :
-- imply
  f.translate p = MvPolynomial.aeval (fun i => X i + C (p i)) f :=
-- proof
  rfl

end MvPolynomial

namespace MvPolynomial

/--
[minTotalDegree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean)
-/
@[path]
lemma minTotalDegree_zero
  [CommRing k] :
-- imply
  (0 : MvPolynomial σ k).minTotalDegree = 0 := by
-- proof
  classical
  simp [minTotalDegree, support_zero]

end MvPolynomial

namespace MvPolynomial

/--
[minTotalDegree_le_totalDegree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean)
-/
@[path]
lemma minTotalDegree_le_totalDegree
  [CommRing k]
  {f : MvPolynomial σ k} :
-- imply
  f.minTotalDegree ≤ f.totalDegree := by
-- proof
  classical
  unfold minTotalDegree
  split_ifs with h
  · set img := f.support.image (fun s => Finsupp.sum s fun _ e => e)
    have hmin_mem : img.min' (h.image _) ∈ img := Finset.min'_mem _ _
    rw [Finset.mem_image] at hmin_mem
    obtain ⟨s, hs, heq⟩ := hmin_mem
    rw [← heq]
    exact le_totalDegree hs
  · exact Nat.zero_le _

end MvPolynomial

namespace MvPolynomial

/--
[translate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean)
-/
@[path]
lemma translate_zero
  [CommRing k]
  {f : MvPolynomial σ k} :
-- imply
  f.translate 0 = f := by
-- proof
  simp only [translate, Pi.zero_apply, map_zero, add_zero]
  change (aeval X) f = f
  rw [aeval_X_left]
  rfl

end MvPolynomial

namespace MvPolynomial

/--
[translate_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean)
-/
@[path]
lemma translate_add
  [CommRing k]
  {p : σ → k}
  {f g : MvPolynomial σ k} :
-- imply
  (f + g).translate p = f.translate p + g.translate p := by
-- proof
  simp [translate]

end MvPolynomial

namespace MvPolynomial

/--
[translate_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MultiplicityDef.lean)
-/
@[path]
lemma translate_mul
  [CommRing k]
  {p : σ → k}
  {f g : MvPolynomial σ k} :
-- imply
  (f * g).translate p = f.translate p * g.translate p := by
-- proof
  simp [translate]

end MvPolynomial


-- created on 2026-10-23
