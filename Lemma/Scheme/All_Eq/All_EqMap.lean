import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_eq_of_forall_map_homOfLE_eq_and_exists_of_compatible.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} (M : X.Modules) {ι : Type u} (U : ι → X.Opens) (V : X.Opens)
  (hUV : ∀ i, U i ≤ V) (hV : V ≤ ⨆ i, U i) :
  -- imply
  (∀ s t : M.presheaf.obj (Opposite.op V), (∀ i, M.presheaf.map (homOfLE (hUV i)).op s = M.presheaf.map (homOfLE (hUV i)).op t) → s = t) ∧ (∀ v : ∀ i, M.presheaf.obj (Opposite.op (U i)), (∀ i j, M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (v i) = M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (v j)) → ∃ s : M.presheaf.obj (Opposite.op V), ∀ i, M.presheaf.map (homOfLE (hUV i)).op s = v i) := by
  -- proof
  let F : TopCat.Sheaf Ab X.carrier := ⟨M.val.presheaf, M.isSheaf⟩
  constructor
  ·
    intro s t h
    apply TopCat.Sheaf.eq_of_locally_eq' F U V (fun i => homOfLE (hUV i)) hV s t h
  ·
    intro v hv
    obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' F U V (fun i => homOfLE (hUV i)) hV v (fun i j => hv i j)
    refine ⟨s, hs⟩


-- created on 2026-10-20
