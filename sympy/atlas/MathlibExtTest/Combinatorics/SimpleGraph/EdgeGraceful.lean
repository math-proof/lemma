/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/SimpleGraph/EdgeGraceful.lean -/


import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import sympy.atlas.Combinatorics.SimpleGraph.EdgeGraceful
import Lemma.SimpleGraph.EdgeGraceful

namespace EdgeGracefulTest

/-- Empty graph is graceful via the canonical empty bijections. -/
example : (⊥ : SimpleGraph Empty).IsEdgeGraceful := by
  classical
  have hE : (⊥ : SimpleGraph Empty).edgeSet = ∅ := SimpleGraph.edgeSet_bot
  have : Fintype (⊥ : SimpleGraph Empty).edgeSet := Fintype.ofFinite _
  have hEmpty : IsEmpty (⊥ : SimpleGraph Empty).edgeSet :=
    Set.isEmpty_coe_sort.mpr hE
  have hc : Fintype.card (⊥ : SimpleGraph Empty).edgeSet = 0 :=
    Fintype.card_eq_zero_iff.mpr hEmpty
  set eLabel : (⊥ : SimpleGraph Empty).edgeSet ≃ Fin 0 :=
    (Fintype.equivFin _).trans (finCongr hc)
  refine ⟨0, eLabel, ?_⟩
  have hfun : (⊥ : SimpleGraph Empty).inducedResidue 0 eLabel =
      ⇑(Fintype.equivFin Empty) :=
    funext fun v => Empty.elim v
  rw [hfun]
  exact (Fintype.equivFin Empty).bijective

/-- Singleton edgeless graph is graceful. -/
example : (⊥ : SimpleGraph (Fin 1)).IsEdgeGraceful := by
  classical
  have hE : (⊥ : SimpleGraph (Fin 1)).edgeSet = ∅ := SimpleGraph.edgeSet_bot
  have : Fintype (⊥ : SimpleGraph (Fin 1)).edgeSet := Fintype.ofFinite _
  have hEmpty : IsEmpty (⊥ : SimpleGraph (Fin 1)).edgeSet :=
    Set.isEmpty_coe_sort.mpr hE
  have hc : Fintype.card (⊥ : SimpleGraph (Fin 1)).edgeSet = 0 :=
    Fintype.card_eq_zero_iff.mpr hEmpty
  set eLabel : (⊥ : SimpleGraph (Fin 1)).edgeSet ≃ Fin 0 :=
    (Fintype.equivFin _).trans (finCongr hc)
  refine ⟨0, eLabel, ?_⟩
  have hp1 : Fintype.card (Fin 1) = 1 := by simp
  have : Subsingleton (Fin 1) := inferInstance
  have : Subsingleton (Fin (Fintype.card (Fin 1))) := hp1.symm ▸ inferInstance
  constructor
  · intro a b h
    exact Subsingleton.elim a b
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩

/-- `K2` is not edge-graceful: both residues coincide. -/
example : ¬ (⊤ : SimpleGraph (Fin 2)).IsEdgeGraceful := by
  classical
  rintro ⟨q, label, hbij⟩
  have hne : Fintype.card (Fin 2) ≠ 0 := by simp
  have hmem : ∀ k : Fin q,
      (0 : Fin 2) ∈ (label.symm k).val ∧ (1 : Fin 2) ∈ (label.symm k).val :=
    fun k => key2 _ (label.symm k).property
  have hsum : (⊤ : SimpleGraph (Fin 2)).incidentSum q label 0 =
      (⊤ : SimpleGraph (Fin 2)).incidentSum q label 1 := by
    unfold SimpleGraph.incidentSum
    apply Finset.sum_congr rfl
    intro k _
    simp only [(hmem k).1, (hmem k).2]
  have hval : ((⊤ : SimpleGraph (Fin 2)).inducedResidue q label 0).val =
      ((⊤ : SimpleGraph (Fin 2)).inducedResidue q label 1).val := by
    rw [SimpleGraph.inducedResidue_val _ q label 0 hne,
      SimpleGraph.inducedResidue_val _ q label 1 hne, hsum]
  have heq01 : (⊤ : SimpleGraph (Fin 2)).inducedResidue q label 0 =
      (⊤ : SimpleGraph (Fin 2)).inducedResidue q label 1 := Fin.ext hval
  have h01 : (0 : Fin 2) = 1 := hbij.injective heq01
  exact (by decide : (0 : Fin 2) ≠ 1) h01

/-- First edge of the 3-vertex path. -/
def e01 : (SimpleGraph.pathGraph 3).edgeSet :=
  ⟨Sym2.mk (0 : Fin 3) 1,
    (SimpleGraph.mem_edgeSet _).mpr (by simp [SimpleGraph.pathGraph_adj])⟩

/-- Second edge of the 3-vertex path. -/
def e12 : (SimpleGraph.pathGraph 3).edgeSet :=
  ⟨Sym2.mk (1 : Fin 3) 2,
    (SimpleGraph.mem_edgeSet _).mpr (by simp [SimpleGraph.pathGraph_adj])⟩

theorem he01 : ((e01 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) =
    Sym2.mk (0 : Fin 3) 1 := rfl

theorem he12 : ((e12 : (SimpleGraph.pathGraph 3).edgeSet) : Sym2 (Fin 3)) =
    Sym2.mk (1 : Fin 3) 2 := rfl

def pathToFun : (SimpleGraph.pathGraph 3).edgeSet → Fin 2 :=
  fun e => if e.val = Sym2.mk (0 : Fin 3) 1 then 0 else 1

def pathInvFun : Fin 2 → (SimpleGraph.pathGraph 3).edgeSet :=
  fun k => if k = 0 then e01 else e12

theorem hto01 : pathToFun e01 = 0 := by simp [pathToFun, he01]

theorem hto12 : pathToFun e12 = 1 := by simp [pathToFun, he12]

theorem hinv0 : pathInvFun 0 = e01 := by simp [pathInvFun]

theorem hinv1 : pathInvFun 1 = e12 := by simp [pathInvFun]

theorem sclass : ∀ s : Sym2 (Fin 3),
    s ∈ (SimpleGraph.pathGraph 3).edgeSet →
      s = Sym2.mk (0 : Fin 3) 1 ∨ s = Sym2.mk (1 : Fin 3) 2 :=
  fun s hs => Sym2.ind (fun a b h => by
    have hadj : (SimpleGraph.pathGraph 3).Adj a b :=
      (SimpleGraph.mem_edgeSet _).mp h
    fin_cases a <;> fin_cases b
    · simp at hadj
    · exact Or.inl rfl
    · simp [SimpleGraph.pathGraph_adj] at hadj
    · exact Or.inl (by decide)
    · simp at hadj
    · exact Or.inr rfl
    · simp [SimpleGraph.pathGraph_adj] at hadj
    · exact Or.inr (by decide)
    · simp at hadj) s hs

theorem eclass : ∀ e : (SimpleGraph.pathGraph 3).edgeSet, e = e01 ∨ e = e12 := by
  intro e
  have h := sclass _ e.property
  rcases h with h | h
  · left
    apply Subtype.ext
    rw [h, he01]
  · right
    apply Subtype.ext
    rw [h, he12]

def pathLabel : (SimpleGraph.pathGraph 3).edgeSet ≃ Fin 2 where
  toFun := pathToFun
  invFun := pathInvFun
  left_inv := by
    intro e
    rcases eclass e with rfl | rfl
    · show pathInvFun (pathToFun e01) = e01
      rw [hto01, hinv0]
    · show pathInvFun (pathToFun e12) = e12
      rw [hto12, hinv1]
  right_inv := by
    intro k
    fin_cases k
    · change pathToFun (pathInvFun 0) = 0
      rw [hinv0, hto01]
    · change pathToFun (pathInvFun 1) = 1
      rw [hinv1, hto12]

/-- The 3-vertex path is graceful with residues `1, 0, 2`. -/
example : (SimpleGraph.pathGraph 3).IsEdgeGraceful := by
  classical
  have hne : Fintype.card (Fin 3) ≠ 0 := by simp
  have hc3 : Fintype.card (Fin 3) = 3 := by simp
  have h0 : (pathLabel.symm 0).val = Sym2.mk (0 : Fin 3) 1 := rfl
  have h1 : (pathLabel.symm 1).val = Sym2.mk (1 : Fin 3) 2 := rfl
  have m00 : (0 : Fin 3) ∈ (pathLabel.symm 0).val := by
    rw [h0]; exact Sym2.mem_mk_left _ _
  have m01 : (0 : Fin 3) ∉ (pathLabel.symm 1).val := by
    rw [h1]; simp only [Sym2.mem_iff]; decide
  have m10 : (1 : Fin 3) ∈ (pathLabel.symm 0).val := by
    rw [h0]; exact Sym2.mem_mk_right _ _
  have m11 : (1 : Fin 3) ∈ (pathLabel.symm 1).val := by
    rw [h1]; exact Sym2.mem_mk_left _ _
  have m20 : (2 : Fin 3) ∉ (pathLabel.symm 0).val := by
    rw [h0]; simp only [Sym2.mem_iff]; decide
  have m21 : (2 : Fin 3) ∈ (pathLabel.symm 1).val := by
    rw [h1]; exact Sym2.mem_mk_right _ _
  have s0 : (SimpleGraph.pathGraph 3).incidentSum 2 pathLabel 0 = 1 := by
    unfold SimpleGraph.incidentSum
    simp [Fin.sum_univ_two, m00, m01]
  have s1 : (SimpleGraph.pathGraph 3).incidentSum 2 pathLabel 1 = 3 := by
    unfold SimpleGraph.incidentSum
    simp [Fin.sum_univ_two, m10, m11]
  have s2 : (SimpleGraph.pathGraph 3).incidentSum 2 pathLabel 2 = 2 := by
    unfold SimpleGraph.incidentSum
    simp [Fin.sum_univ_two, m20, m21]
  have r0 : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel 0).val = 1 := by
    rw [SimpleGraph.inducedResidue_val _ 2 pathLabel 0 hne, s0, hc3]
  have r1 : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel 1).val = 0 := by
    rw [SimpleGraph.inducedResidue_val _ 2 pathLabel 1 hne, s1, hc3]
  have r2 : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel 2).val = 2 := by
    rw [SimpleGraph.inducedResidue_val _ 2 pathLabel 2 hne, s2, hc3]
  refine ⟨2, pathLabel, ?_⟩
  have e0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have e1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have e2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have hfun : ((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) =
      ⇑((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) := by
    funext x
    fin_cases x
    · apply Fin.ext
      change ((((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) 0).val) =
        (((((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) 0)).val)
      rw [r0]
      simp [Equiv.trans_apply, e0]
    · apply Fin.ext
      change ((((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) 1).val) =
        (((((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) 1)).val)
      rw [r1]
      simp [Equiv.trans_apply, e1]
    · apply Fin.ext
      change ((((SimpleGraph.pathGraph 3).inducedResidue 2 pathLabel) 2).val) =
        (((((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)) 2)).val)
      rw [r2]
      simp [Equiv.trans_apply, e2]
  rw [hfun]
  exact ((Equiv.swap (0 : Fin 3) 1).trans (finCongr hc3.symm)).bijective

end EdgeGracefulTest
