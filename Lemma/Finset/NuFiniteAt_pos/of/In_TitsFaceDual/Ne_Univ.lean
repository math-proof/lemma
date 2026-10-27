import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.Buildings.code.AffineCoxeter.TitsConeFiniteParabolic.Part4
open Finset CoxeterGroup TitsCone


/--
[face_subset_nuFinite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/AffineCoxeter/TitsConeFiniteParabolic.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} [RootSystemData M]
  {I : Finset B}
  {x : B → ℝ}
-- given
  (hI : I ≠ Finset.univ)
  (hx : x ∈ titsFaceDual M I) :
-- imply
  nuFiniteAt (RootSystemData.Φpos (M := M)) x := by
-- proof
  unfold nuFiniteAt nonposRoots
  apply Set.Finite.subset (RootSystemData.roots_in_subspan_finite (M := M) I hI)
  intro α ⟨hαpos, hαpair⟩
  refine ⟨hαpos, ?_⟩
  intro s hs
  by_contra hne
  have hpos := RootSystemData.pos_pairing_outside_span I x hx α hαpos ⟨s, hs, hne⟩
  linarith


-- created on 2026-10-24
