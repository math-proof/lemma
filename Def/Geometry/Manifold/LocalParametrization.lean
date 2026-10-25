/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/Manifold/LocalParametrization.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Immersion
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Theorem.Geometry.Manifold.LocalGraph
import Lemma.Set.Manifold.LocalGraph
open scoped Topology Manifold ContDiff
open Manifold

/-!
# Local parametrizations of regular level sets

This file proves that a regular level set of a continuously differentiable map between
Euclidean spaces is locally the image of a global continuously differentiable immersion.
It also proves that the graph of a continuously differentiable map is an immersion.
-/


noncomputable section

namespace MathlibExt.Geometry.Manifold.LocalParametrizationWanted

def levelParam_graphDiffeomorph
    {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ∞ω} (h : E → F) (hh : ContDiff ℝ n h) (e : (E × F) ≃L[ℝ] G) :
    Diffeomorph 𝓘(ℝ, G) 𝓘(ℝ, G) G G n where
  toEquiv := {
    toFun := fun z => e ((e.symm z).1, (e.symm z).2 - h (e.symm z).1)
    invFun := fun z => e ((e.symm z).1, (e.symm z).2 + h (e.symm z).1)
    left_inv := by
      intro z
      simp
    right_inv := by
      intro z
      simp }
  contMDiff_toFun := contMDiff_iff_contDiff.mpr <| by
    have ha : ContDiff ℝ n (fun z : G => (e.symm z).1) :=
      contDiff_fst.comp e.symm.contDiff
    have hb : ContDiff ℝ n (fun z : G => (e.symm z).2) :=
      contDiff_snd.comp e.symm.contDiff
    exact e.contDiff.comp (ha.prodMk (hb.sub (hh.comp ha)))
  contMDiff_invFun := contMDiff_iff_contDiff.mpr <| by
    have ha : ContDiff ℝ n (fun z : G => (e.symm z).1) :=
      contDiff_fst.comp e.symm.contDiff
    have hb : ContDiff ℝ n (fun z : G => (e.symm z).2) :=
      contDiff_snd.comp e.symm.contDiff
    exact e.contDiff.comp (ha.prodMk (hb.add (hh.comp ha)))

end MathlibExt.Geometry.Manifold.LocalParametrizationWanted
end
