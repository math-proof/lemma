import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma helper_main
  {X Y : (Scheme : Type (u + 1))} (p : X ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (y : Y) (hy : y ∈ U)
  (s : X.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U))) (hs : ∀ x : X, p.base x = y → x ∈ X.basicOpen s) :
  ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧ (TopologicalSpace.Opens.map p.base).obj V.1 ≤ X.basicOpen s := by
  have hFc : IsClosed ((X.basicOpen s : Set X)ᶜ) := (X.basicOpen s).2.isClosed_compl
  have hIm : IsClosed (p.base '' ((X.basicOpen s : Set X)ᶜ)) := p.isClosedMap _ hFc
  have hyn : y ∉ p.base '' ((X.basicOpen s : Set X)ᶜ) := by
    rintro ⟨x, hx, hxy⟩
    apply hx (hs x hxy)
  let W : Y.Opens := U ⊓ ⟨(p.base '' ((X.basicOpen s : Set X)ᶜ))ᶜ, hIm.isOpen_compl⟩
  have hyW : y ∈ (W : Set Y) := ⟨hy, hyn⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hyW W.2
  refine ⟨⟨V, hV⟩, hyV, fun v hv => (hVW hv).1, fun x hx => ?_⟩
  by_contra hxs
  apply (hVW hx).2 ⟨x, hxs, rfl⟩
/--
[AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_affineOpens_le_preimage_le_basicOpen_of_universallyClosed.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (p : X ⟶ Y) [UniversallyClosed p] (U : Y.Opens) (y : Y) (hy : y ∈ U)
  (s : X.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map p.base).obj U))) (hs : ∀ x : X, p.base x = y → x ∈ X.basicOpen s) :
  -- imply
  ∃ V : Y.affineOpens, y ∈ V.1 ∧ V.1 ≤ U ∧ (TopologicalSpace.Opens.map p.base).obj V.1 ≤ X.basicOpen s :=
  helper_main p U y hy s hs


-- created on 2026-10-20
