import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u


/--
[AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_fibrePower_represents_tuples.lean)
-/
@[path]
private lemma main
  {B Y : (Scheme : Type (u + 1))} (πY : Y ⟶ B) (n : ℕ) :
  ∃ (P : (Scheme : Type (u + 1))) (πP : P ⟶ B) (q : Fin n → (P ⟶ Y)), (∀ l, q l ≫ πY = πP) ∧
    (∀ (T : (Scheme : Type (u + 1))) (t : T ⟶ B) (g : Fin n → (T ⟶ Y)), (∀ l, g l ≫ πY = t) →
      ∃! G : T ⟶ P, G ≫ πP = t ∧ ∀ l, G ≫ q l = g l) ∧
    (IsSeparated πY → IsSeparated πP) ∧
    (LocallyOfFiniteType πY → LocallyOfFiniteType πP) ∧
    (LocallyOfFinitePresentation πY → LocallyOfFinitePresentation πP) ∧
    (∀ U : Fin n → Y.Opens, (∀ l, IsClosed ((U l : Set Y))) → (∀ l, QuasiCompact ((U l).ι ≫ πY)) →
      IsClosed ((⨅ l, ((TopologicalSpace.Opens.map (q l).base).obj (U l)) : P.Opens) : Set P) ∧
      QuasiCompact (Scheme.Opens.ι (⨅ l, ((TopologicalSpace.Opens.map (q l).base).obj (U l))) ≫ πP)) := by
  classical
  have coe_iInf : ∀ {Z : (Scheme : Type (u + 1))} {k : ℕ} (V : Fin k → Z.Opens), ((⨅ j, V j : Z.Opens) : Set Z) = ⋂ j, (V j : Set Z) := by
    intro Z k V
    rw [← Finset.inf_univ_eq_iInf, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_univ_eq_iInf,
      Set.iInf_eq_iInter]
    rfl
  have preimage_iInf : ∀ {Z Z' : (Scheme : Type (u + 1))} (g : Z ⟶ Z') {k : ℕ} (V : Fin k → Z'.Opens), ((TopologicalSpace.Opens.map g.base).obj (⨅ j, V j)) = ⨅ j, ((TopologicalSpace.Opens.map g.base).obj (V j)) := by
    intro Z Z' g k V
    apply TopologicalSpace.Opens.ext
    rw [coe_iInf, Scheme.Hom.coe_preimage, coe_iInf, Set.preimage_iInter]
    rfl
  have iInf_snoc : ∀ {Z : (Scheme : Type (u + 1))} {k : ℕ} (F : Fin (k + 1) → Z.Opens), (⨅ l, F l) = (⨅ i : Fin k, F i.castSucc) ⊓ F (Fin.last k) := by
    intro Z k F
    apply le_antisymm
    · apply le_inf (le_iInf fun i => iInf_le _ _) (iInf_le _ _)
    · apply le_iInf fun l => Fin.lastCases inf_le_right (fun i => inf_le_left.trans (iInf_le _ i)) l
  induction n with
  | zero =>
    refine ⟨B, 𝟙 B, fun l => l.elim0, fun l => l.elim0, ?_, fun _ => inferInstance, fun _ => inferInstance,
      fun _ => inferInstance, ?_⟩
    ·
      intro T t g hg
      refine ⟨t, ⟨Category.comp_id t, fun l => l.elim0⟩, fun G hG => ?_⟩
      rw [← hG.1, Category.comp_id]
    ·
      intro U hUc hUq
      have htop : (⨅ l, ((TopologicalSpace.Opens.map (Fin.elim0 l : B ⟶ Y).base).obj (U l)) : B.Opens) = ⊤ :=
        le_antisymm le_top (le_iInf fun l => l.elim0)
      rw [htop]
      have hclosed : IsClosed ((⊤ : B.Opens) : Set B) := by
        rw [TopologicalSpace.Opens.coe_top]
        apply isClosed_univ
      refine ⟨hclosed, ?_⟩
      rw [Category.comp_id, ← Scheme.topIso_hom]
      infer_instance
  | succ n ih =>
    obtain ⟨P, πP, q, hq, huniv, hsep, hlft, hlfp, hpieces⟩ := ih
    refine ⟨pullback πP πY, pullback.fst πP πY ≫ πP,
      Fin.snoc (α := fun _ => (pullback πP πY ⟶ Y)) (fun i => pullback.fst πP πY ≫ q i) (pullback.snd πP πY),
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro l
      refine Fin.lastCases ?_ (fun i => ?_) l
      ·
        simp only [Fin.snoc_last]
        apply pullback.condition.symm
      · simp only [Fin.snoc_castSucc, Category.assoc, hq]
    ·
      intro T t g hg
      obtain ⟨G₀, ⟨hG₀t, hG₀q⟩, hG₀u⟩ := huniv T t (fun i => g i.castSucc) (fun i => hg i.castSucc)
      refine ⟨pullback.lift G₀ (g (Fin.last n)) (by rw [hG₀t, hg]), ⟨?_, ?_⟩, ?_⟩
      · rw [pullback.lift_fst_assoc, hG₀t]
      ·
        intro l
        refine Fin.lastCases ?_ (fun i => ?_) l
        · simp only [Fin.snoc_last, pullback.lift_snd]
        · simp only [Fin.snoc_castSucc, pullback.lift_fst_assoc, hG₀q]
      ·
        rintro G ⟨hGt, hGq⟩
        apply pullback.hom_ext
        ·
          rw [pullback.lift_fst]
          apply hG₀u
          refine ⟨by rwa [Category.assoc], fun i => ?_⟩
          have h := hGq i.castSucc
          simp only [Fin.snoc_castSucc] at h
          rwa [Category.assoc]
        ·
          rw [pullback.lift_snd]
          have h := hGq (Fin.last n)
          simp only [Fin.snoc_last] at h
          apply h
    ·
      intro h
      let := h
      let := hsep h
      infer_instance
    ·
      intro h
      let := h
      let := hlft h
      infer_instance
    ·
      intro h
      let := h
      let := hlfp h
      infer_instance
    ·
      intro U hUc hUq
      obtain ⟨hVc, hVq⟩ := hpieces (fun i => U i.castSucc) (fun i => hUc _) (fun i => hUq _)
      generalize hV : (⨅ i, ((TopologicalSpace.Opens.map (q i).base).obj (U i.castSucc)) : P.Opens) = V at hVc hVq
      have hW : (⨅ l, ((TopologicalSpace.Opens.map (Fin.snoc (α := fun _ => (pullback πP πY ⟶ Y)) (fun i => pullback.fst πP πY ≫ q i) (pullback.snd πP πY) l).base).obj (U l)) : (pullback πP πY).Opens) =
          ((TopologicalSpace.Opens.map (pullback.fst πP πY).base).obj V) ⊓ ((TopologicalSpace.Opens.map (pullback.snd πP πY).base).obj (U (Fin.last n))) := by
        rw [iInf_snoc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        rw [← hV, preimage_iInf]
        rfl
      rw [hW]
      refine ⟨?_, ?_⟩
      ·
        rw [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage, Scheme.Hom.coe_preimage]
        apply (hVc.preimage (pullback.fst πP πY).continuous).inter ((hUc (Fin.last n)).preimage (pullback.snd πP πY).continuous)
      ·
        let _ := hVq
        let _ := hUq (Fin.last n)
        let j := pullback.map (V.ι ≫ πP) ((U (Fin.last n)).ι ≫ πY) πP πY V.ι (U (Fin.last n)).ι (𝟙 B)
          (Category.comp_id _) (Category.comp_id _)
        have hrange : Set.range j =
            Set.range (Scheme.Opens.ι (((TopologicalSpace.Opens.map (pullback.fst πP πY).base).obj V) ⊓ ((TopologicalSpace.Opens.map (pullback.snd πP πY).base).obj (U (Fin.last n))))) := by
          rw [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage,
            Scheme.Hom.coe_preimage]
          rw [Scheme.Pullback.range_map, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
        have hfac : Scheme.Opens.ι (((TopologicalSpace.Opens.map (pullback.fst πP πY).base).obj V) ⊓ ((TopologicalSpace.Opens.map (pullback.snd πP πY).base).obj (U (Fin.last n)))) ≫ pullback.fst πP πY ≫ πP = (IsOpenImmersion.isoOfRangeEq j _ hrange).inv ≫ pullback.fst (V.ι ≫ πP) ((U (Fin.last n)).ι ≫ πY) ≫ (V.ι ≫ πP) := by
          nth_rw 1 [← IsOpenImmersion.isoOfRangeEq_inv_fac j _ hrange]
          simp only [Category.assoc, j, pullback.map, pullback.lift_fst_assoc]
        rw [hfac]
        infer_instance


-- created on 2026-10-20
