import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite IsLocalRing TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_existsUnique_germToFunctionField_eq_of_iSup_eq.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} [IsIntegral X] {ι : Type u} (V : ι → X.Opens) [hVi : ∀ i, Nonempty (V i)] (W : X.Opens) [hW : Nonempty W] (hV : iSup V = W)
  (f : X.functionField) (s : ∀ i, X.presheaf.obj (Opposite.op (V i))) (hs : ∀ i, X.germToFunctionField (V i) (s i) = f) :
  -- imply
  ∃! t : X.presheaf.obj (Opposite.op W), X.germToFunctionField W t = f ∧ ∀ i, X.presheaf.map (homOfLE (hV ▸ le_iSup V i : V i ≤ W)).op t = s i := by
  -- proof
  classical
  have hle : ∀ i, V i ≤ W := fun i => hV ▸ le_iSup V i
  have germ_res : ∀ {A B : X.Opens} (hA : Nonempty A) (hB : Nonempty B) (h : A ≤ B) (x : X.presheaf.obj (Opposite.op B)), @Scheme.germToFunctionField X _ A hA (X.presheaf.map (homOfLE h).op x) = @Scheme.germToFunctionField X _ B hB x := by
    intro A B _ _ h x
    apply TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE h) (genericPoint X) _ x
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf V s := by
    intro i j
    if hne : Nonempty ↥(V i ⊓ V j) then
      apply @Scheme.germToFunctionField_injective X _ (V i ⊓ V j) hne
      rw [show X.presheaf.map (Opens.infLELeft (V i) (V j)).op (s i) = X.presheaf.map (homOfLE (inf_le_left : V i ⊓ V j ≤ V i)).op (s i) from rfl, show X.presheaf.map (Opens.infLERight (V i) (V j)).op (s j) = X.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (s j) from rfl, germ_res hne (hVi i), germ_res hne (hVi j), hs, hs]
    else
      have hbot : V i ⊓ V j = ⊥ := by
        ext x
        simp only [Opens.coe_inf, Set.mem_inter_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
        intro hxi hxj
        apply hne ⟨⟨x, ⟨hxi, hxj⟩⟩⟩
      let _ : Subsingleton (X.presheaf.obj (Opposite.op (V i ⊓ V j))) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty (by rw [hbot]))
      apply Subsingleton.elim _ _
  obtain ⟨t, ht, huniq⟩ := X.sheaf.existsUnique_gluing' V W (fun i => homOfLE (hle i)) (le_of_eq hV.symm) s hcompat
  have ht' : ∀ i, X.presheaf.map (homOfLE (hle i)).op t = s i := ht
  obtain ⟨i₀⟩ : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    have : W = ⊥ := by
      rw [← hV, iSup_of_empty]
    let w : W := Classical.choice hW
    rw [this] at w
    apply w.2
  have hgerm : X.germToFunctionField W t = f := by
    rw [← germ_res (hVi i₀) hW (hle i₀) t, ht' i₀, hs]
  refine ExistsUnique.intro t (And.intro hgerm (fun i => ht' i)) (fun t' ht'' => huniq t' (And.right ht''))


-- created on 2026-10-20
