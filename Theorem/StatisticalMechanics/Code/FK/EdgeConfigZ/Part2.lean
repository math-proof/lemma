/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Def.StatisticalMechanics.Code.FK.EdgeConfigZ.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section EdgeZ

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ecz_NE_eq : ecz_NE G = Fintype.card (Sym2 V) - G.edgeFinset.card := by
  unfold ecz_NE
  rw [Finset.filter_not, Finset.card_univ_diff]
  congr 1
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]


theorem ecz_fkZEdge_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 < ecz_fkZEdge G p q :=
  Finset.sum_pos (fun ω _ => fkWeight_pos G hp hp1 hq ω.val) Finset.univ_nonempty

theorem ecz_fkZEdge_ne_zero {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    ecz_fkZEdge G p q ≠ 0 :=
  (ecz_fkZEdge_pos G hp hp1 hq).ne'


theorem ecz_factorization (p q : ℝ) :
    fkZ G p q = 2 ^ ecz_NE G * ecz_fkZEdge G p q := by
  classical
  set P : Sym2 V → Prop := fun e => e ∈ G.edgeFinset with hP
  rw [fkZ, ← Equiv.sum_comp (Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm
        (fun ω => fkWeight G p q ω), Fintype.sum_prod_type]
  rw [ecz_fkZEdge]
  have hcard : (Fintype.card ({e // ¬ P e} → Bool))
      = 2 ^ (Finset.univ.filter (fun e : Sym2 V => e ∉ G.edgeFinset)).card := by
    rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype]
  have key : ∀ η : ({e // P e} → Bool),
      (∑ ξ : ({e // ¬ P e} → Bool),
        fkWeight G p q ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (η, ξ)))
      = 2 ^ ecz_NE G
          * fkWeight G p q ((Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (η, fun _ => false)) := by
    intro η
    rw [Finset.sum_congr rfl (fun ξ _ => ?_)]
    · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, ecz_NE]; push_cast; ring
    · apply ecz_fkWeight_eq_of_edges
      intro e he
      rw [Equiv.piEquivPiSubtypeProd_symm_apply, Equiv.piEquivPiSubtypeProd_symm_apply,
        dif_pos he, dif_pos he]
  rw [Finset.sum_congr rfl (fun η _ => key η), ← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_nbij'
    (i := fun ω : ecz_ClosedOff G => (fun e : {e // P e} => ω.val e.val))
    (j := fun η : ({e // P e} → Bool) =>
      (⟨(Equiv.piEquivPiSubtypeProd P (fun _ => Bool)).symm (η, fun _ => false), by
        intro e he
        rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg he]⟩ : ecz_ClosedOff G))
    (fun ω _ => Finset.mem_univ _) (fun η _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro ω _
    apply Subtype.ext
    ext e
    by_cases he : P e
    · simp only; rw [Equiv.piEquivPiSubtypeProd_symm_apply]; simp [he]
    · simp only; rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg he]
      exact (ω.2 e he).symm
  · intro η _
    ext e
    simp only
    rw [Equiv.piEquivPiSubtypeProd_symm_apply]; simp [e.2]
  · intro ω _
    apply ecz_fkWeight_eq_of_edges
    intro e he
    rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos he]


theorem ecz_fkZEdge_eq_div (p q : ℝ) :
    ecz_fkZEdge G p q = fkZ G p q / 2 ^ ecz_NE G := by
  rw [ecz_factorization G p q]
  have : (2 : ℝ) ^ ecz_NE G ≠ 0 := by positivity
  field_simp

end EdgeZ


section Iso

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]


theorem ecz_NE_iso (φ : G ≃g H) : ecz_NE G = ecz_NE H := by
  rw [ecz_NE_eq, ecz_NE_eq, Fintype.card_congr (fsm_sym2Congr φ.toEquiv), φ.card_edgeFinset_eq]


theorem ecz_fkZEdge_iso (φ : G ≃g H) (p q : ℝ) :
    ecz_fkZEdge G p q = ecz_fkZEdge H p q := by
  have hZ : fkZ G p q = fkZ H p q := fsm_fkZ_iso G H φ p q
  rw [ecz_fkZEdge_eq_div, ecz_fkZEdge_eq_div, ecz_NE_iso φ, hZ]

end Iso


section Interface

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
  {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel G.Adj] [DecidableRel H.Adj]
  {K : SimpleGraph (V ⊕ W)} [DecidableRel K.Adj]


theorem ecz_combine_closedOff (hci : fis_CrossInterface G H K)
    (σ : ecz_ClosedOff G) (τ : ecz_ClosedOff H) (e : Sym2 (V ⊕ W)) (he : e ∉ K.edgeFinset) :
    fsm_combine σ.val τ.val e = false := by
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    match x, y with
    | Sum.inl a, Sum.inl b =>
      show σ.val s(a, b) = false
      apply σ.2
      rw [mem_edgeFinset, mem_edgeSet]
      intro hG
      exact he (hci.le (show (G ⊕g H).Adj (Sum.inl a) (Sum.inl b) from hG))
    | Sum.inr c, Sum.inr d =>
      show τ.val s(c, d) = false
      apply τ.2
      rw [mem_edgeFinset, mem_edgeSet]
      intro hH
      exact he (hci.le (show (G ⊕g H).Adj (Sum.inr c) (Sum.inr d) from hH))
    | Sum.inl a, Sum.inr d => rfl
    | Sum.inr c, Sum.inl b => rfl


theorem ecz_fkZEdge_interface_ge (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q := by
  classical
  let glue : ecz_ClosedOff G → ecz_ClosedOff H → ecz_ClosedOff K :=
    fun σ τ => ⟨fsm_combine σ.val τ.val, ecz_combine_closedOff hci σ τ⟩
  have hprod : (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      = ∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (glue στ.1 στ.2).val := by
    rw [ecz_fkZEdge, ecz_fkZEdge, Fintype.sum_mul_sum, Finset.mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    show _ = fkWeight K p q (fsm_combine σ.val τ.val)
    rw [fis_fkWeight_combine hci p q σ.val τ.val]
  rw [hprod]
  have hinj : Function.Injective
      (fun στ : ecz_ClosedOff G × ecz_ClosedOff H => glue στ.1 στ.2) := by
    rintro ⟨σ₁, τ₁⟩ ⟨σ₂, τ₂⟩ h
    have heq : fsm_combine σ₁.val τ₁.val = fsm_combine σ₂.val τ₂.val := congrArg Subtype.val h
    have h2 : ((σ₁.val, τ₁.val) : (Sym2 V → Bool) × (Sym2 W → Bool)) = (σ₂.val, τ₂.val) :=
      fsm_combine_injective heq
    rw [Prod.mk.injEq] at h2
    exact Prod.ext (Subtype.ext h2.1) (Subtype.ext h2.2)
  rw [ecz_fkZEdge,
    show (∑ στ : ecz_ClosedOff G × ecz_ClosedOff H, fkWeight K p q (glue στ.1 στ.2).val)
        = ∑ ω ∈ Finset.univ.image (fun στ : ecz_ClosedOff G × ecz_ClosedOff H => glue στ.1 στ.2),
            fkWeight K p q ω.val from by
      rw [Finset.sum_image]; intro a _ b _ h; exact hinj h]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro ω _ _
  exact fkWeight_nonneg K hp hp1 hq ω.val


theorem ecz_neglog_interface_le (hci : fis_CrossInterface G H K) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    - Real.log (ecz_fkZEdge K p q)
      ≤ - Real.log (ecz_fkZEdge G p q) + - Real.log (ecz_fkZEdge H p q)
        - (fis_interface G H K).card * Real.log (1 - p) := by
  have hZG : 0 < ecz_fkZEdge G p q := ecz_fkZEdge_pos G hp hp1 hq
  have hZH : 0 < ecz_fkZEdge H p q := ecz_fkZEdge_pos H hp hp1 hq
  have hZK : 0 < ecz_fkZEdge K p q := ecz_fkZEdge_pos K hp hp1 hq
  have h1mp : (0:ℝ) < 1 - p := by linarith
  have hge : (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q)
      ≤ ecz_fkZEdge K p q := ecz_fkZEdge_interface_ge hci hp hp1 hq
  have hpos : 0 < (1 - p) ^ (fis_interface G H K).card * (ecz_fkZEdge G p q * ecz_fkZEdge H p q) :=
    mul_pos (pow_pos h1mp _) (mul_pos hZG hZH)
  have hlog : Real.log ((1 - p) ^ (fis_interface G H K).card
        * (ecz_fkZEdge G p q * ecz_fkZEdge H p q))
      ≤ Real.log (ecz_fkZEdge K p q) := Real.log_le_log hpos hge
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hZG.ne' hZH.ne',
    Real.log_pow] at hlog
  push_cast at hlog ⊢
  linarith

end Interface


section AllClosed

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem ecz_fkZEdge_ge_allClosed {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    (1 - p) ^ G.edgeFinset.card ≤ ecz_fkZEdge G p q := by
  have hterm : (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := by
    unfold fkWeight edgeProduct
    have hep : (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
        = (1 - p) ^ G.edgeFinset.card := by
      rw [show (∏ e ∈ G.edgeFinset, (if (fun (_ : Sym2 V) => false) e then p else 1 - p))
            = ∏ _e ∈ G.edgeFinset, (1 - p) from Finset.prod_congr rfl (fun e _ => by simp),
        Finset.prod_const]
    rw [hep]
    have hqk : (1 : ℝ) ≤ q ^ numClusters G (fun _ => false) := one_le_pow₀ hq1
    nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) G.edgeFinset.card]
  calc (1 - p) ^ G.edgeFinset.card ≤ fkWeight G p q (fun _ => false) := hterm
    _ = fkWeight G p q (⟨fun _ => false, fun _ _ => rfl⟩ : ecz_ClosedOff G).val := rfl
    _ ≤ ecz_fkZEdge G p q := by
        unfold ecz_fkZEdge
        exact Finset.single_le_sum (f := fun ω : ecz_ClosedOff G => fkWeight G p q ω.val)
          (fun ω _ => fkWeight_nonneg G hp hp1 (by linarith) ω.val) (Finset.mem_univ _)


theorem ecz_neglogZEdge_le_edges {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq1 : 1 ≤ q) :
    -Real.log (ecz_fkZEdge G p q) ≤ (G.edgeFinset.card : ℝ) * (-Real.log (1 - p)) := by
  have h1mp : (0 : ℝ) < 1 - p := by linarith
  have hge := ecz_fkZEdge_ge_allClosed G hp hp1 hq1
  have hpow : (0 : ℝ) < (1 - p) ^ G.edgeFinset.card := pow_pos h1mp _
  have hZ : 0 < ecz_fkZEdge G p q := ecz_fkZEdge_pos G hp hp1 (by linarith)
  have hlog : Real.log ((1 - p) ^ G.edgeFinset.card) ≤ Real.log (ecz_fkZEdge G p q) :=
    Real.log_le_log hpow hge
  rw [Real.log_pow] at hlog
  push_cast at hlog ⊢
  nlinarith [hlog]

end AllClosed


section PartitionPeel

variable {U : Type*} [Fintype U] [DecidableEq U] (K₀ : SimpleGraph U) [DecidableRel K₀.Adj]


theorem ecz_neglog_partition_le (P : U → Prop) [DecidablePred P] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    -Real.log (ecz_fkZEdge K₀ p q)
      ≤ -Real.log (ecz_fkZEdge (agl_left K₀ P) p q)
        + -Real.log (ecz_fkZEdge (agl_right K₀ P) p q)
        - (agl_interfaceCard K₀ P : ℝ) * Real.log (1 - p) := by
  have hiso : ecz_fkZEdge K₀ p q = ecz_fkZEdge (agl_glueGraph K₀ P) p q :=
    ecz_fkZEdge_iso (agl_iso K₀ P) p q
  rw [hiso]
  exact ecz_neglog_interface_le (agl_partitionCrossInterface K₀ P) hp hp1 hq


end PartitionPeel
end FK
end StatMech
