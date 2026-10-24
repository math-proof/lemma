import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.SphericalBuilding.AdaptedBasisSingle
open GLnBuilding
open Submodule Module


/--
[frameOfBasis_lines](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisSingle.lean)
-/
@[path]
private lemma main
  {k : Type*}
  [Field k]
  {n : ℕ}
  {b : Basis (Fin n) k (Vec k n)}
  {i : Fin n} :
-- imply
  (frameOfBasis k n b).lines i = k ∙ b i :=
-- proof
  rfl



/--
[adapted_frame_of_single_subspace](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/AdaptedBasisSingle.lean)
-/
private lemma adapted_frame_of_single_subspace
  {k : Type*}
  [Field k]
  {n : ℕ}
  {V : Submodule k (Vec k n)}
-- given
  (_hbot : V ≠ ⊥)
  (_htop : V ≠ ⊤) :
-- imply
  ∃ F : Frame k n, F.IsCompatible k n V := by
-- proof
  obtain ⟨W, hVW⟩ := V.exists_isCompl
  set d := finrank k V with hd_def
  set e := finrank k W with he_def
  have hde : d + e = n := by
    have := Submodule.finrank_add_eq_of_isCompl hVW
    rw [finrank_fin_fun] at this; exact this
  have bV : Basis (Fin d) k V := finBasis k V
  have bW : Basis (Fin e) k W := finBasis k W
  let bVW := bV.prod bW
  let bAll := bVW.map (prodEquivOfIsCompl V W hVW)
  let idx : Fin d ⊕ Fin e ≃ Fin n := finSumFinEquiv.trans (finCongr hde)
  let b := bAll.reindex idx
  use frameOfBasis k n b
  use Finset.image (fun i : Fin d => idx (Sum.inl i)) Finset.univ
  rw [Finset.iSup_finset_image]
  simp only [Finset.mem_univ, iSup_true]
  have key : ∀ j : Fin d, b (idx (Sum.inl j)) = V.subtype (bV j) := by
    intro j
    simp [b, bAll, bVW, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply,
      prodEquivOfIsCompl]
  simp_rw [frameOfBasis_lines, key]
  rw [← span_range_eq_iSup]
  rw [show (fun j => V.subtype (bV j)) = V.subtype ∘ bV from rfl]
  rw [Set.range_comp, Submodule.span_image, bV.span_eq]
  exact (map_subtype_top V).symm



-- created on 2026-10-23
-- updated on 2026-10-24
