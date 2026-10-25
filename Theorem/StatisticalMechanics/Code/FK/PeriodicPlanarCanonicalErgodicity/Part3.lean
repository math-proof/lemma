/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalTranslation.Part4
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part2
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal StatMech symmDiff


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice

variable {V : Type*} [Countable V] [DecidableEq V]


omit [Countable V] in
theorem PeriodicGraph.bufferedEdgeWindow_endpoint
    (P : PeriodicGraph V) {N : ℕ} {e : Sym2 V}
    (he : e ∈ P.bufferedEdgeWindow N) {x : V} (hx : x ∈ e) :
    x ∈ P.orbitBox (P.bufferedRadius N) := by
  obtain ⟨eN, rfl⟩ := he
  induction eN using Sym2.inductionOn with
  | _ u v =>
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact u.2
      · exact v.2

omit [Countable V] in
theorem PeriodicGraph.mem_edgeVertexFinset_of_mem
    (P : PeriodicGraph V) {F : Finset (Sym2 V)} {e : Sym2 V}
    (he : e ∈ F) {x : V} (hx : x ∈ e) :
    x ∈ PeriodicGraph.edgeVertexFinset F := by
  rw [PeriodicGraph.edgeVertexFinset, Finset.mem_biUnion]
  exact ⟨e, he, by simpa using hx⟩

theorem exists_finset_abs_bound
    (S : Finset V) (f : V → ℝ) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ S, |f x| ≤ R := by
  classical
  refine ⟨∑ x ∈ S, |f x|, Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  intro x hx
  exact Finset.single_le_sum (fun y _ => abs_nonneg (f y)) hx


theorem PeriodicPlaneEmbedding.bufferedEdgeWindow_escape
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    (F : Finset (Sym2 V)) (k : ℕ) :
    letI : SMul (Multiplicative (Site 2)) (Sym2 V) :=
      ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩
    ∃ g : Multiplicative (Site 2),
      (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 V)) ⊆
        (P.bufferedEdgeWindow k)ᶜ := by
  classical
  letI : SMul (Multiplicative (Site 2)) (Sym2 V) :=
    ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩
  let VF := PeriodicGraph.edgeVertexFinset F
  let VK := P.orbitBox (P.bufferedRadius k)
  obtain ⟨RF, hRF0, hRF⟩ :=
    exists_finset_abs_bound VF (fun x => E.vertexCoord x 0)
  obtain ⟨RK, hRK0, hRK⟩ :=
    exists_finset_abs_bound VK (fun x => E.vertexCoord x 0)
  obtain ⟨L : ℕ, hL⟩ := exists_nat_gt (RF + RK)
  let z : Site 2 := fun i => if i = 0 then (L : ℤ) else 0
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd z
  refine ⟨g, ?_⟩
  intro e he
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at he
  obtain ⟨e0, he0, rfl⟩ := he
  rw [Set.mem_compl_iff]
  intro hwindow
  induction e0 using Sym2.inductionOn with
  | _ x y =>
      have hxVF : x ∈ VF :=
        P.mem_edgeVertexFinset_of_mem he0 (Sym2.mem_mk_left x y)
      have hxBound : E.vertexCoord x 0 ≤ RF :=
        (le_abs_self _).trans (hRF x hxVF)
      have hxShiftMem : P.shift (-z) x ∈
          P.orbitBox (P.bufferedRadius k) := by
        apply P.bufferedEdgeWindow_endpoint hwindow
        change P.shift (-z) x ∈
          Sym2.map (P.shift (Multiplicative.toAdd g⁻¹)) s(x, y)
        have hginv : Multiplicative.toAdd g⁻¹ = -z := rfl
        rw [hginv, Sym2.map_mk]
        exact Sym2.mem_mk_left _ _
      have hxTarget : -RK ≤ E.vertexCoord (P.shift (-z) x) 0 := by
        have habs := hRK (P.shift (-z) x) hxShiftMem
        exact (neg_le_of_abs_le habs)
      have hz0 : z 0 = (L : ℤ) := by simp [z]
      have hcoord : E.vertexCoord (P.shift (-z) x) 0 =
          E.vertexCoord x 0 - L := by
        rw [E.vertexCoord_shift]
        simp [hz0]
        ring
      rw [hcoord] at hxTarget
      have hLreal : RF + RK < (L : ℝ) := by exact_mod_cast hL
      linarith


theorem PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_isErgodic
    {P : PeriodicGraph V} (E : PeriodicPlaneEmbedding P)
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    P.IsErgodic
      (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
  let mu := (P.freeBufferedInfiniteVolume hp hp1
    (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 V)))
  have hTI := P.freeBufferedInfiniteVolume_isTranslationInvariant hp hp1 hq
  refine ⟨hTI, ?_⟩
  intro s hs hinv
  letI : SMul (Multiplicative (Site 2)) (Sym2 V) :=
    ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩
  letI : SemigroupAction (Multiplicative (Site 2)) (Sym2 V) := ⟨by
    intro g h e
    change Sym2.map (P.shift (g * h).toAdd) e =
      Sym2.map (P.shift g.toAdd) (Sym2.map (P.shift h.toAdd) e)
    induction e using Sym2.inductionOn with
    | _ x y =>
        simp only [Sym2.map_mk]
        rw [show (g * h).toAdd = g.toAdd + h.toAdd from rfl]
        congr 1
        · exact (by simpa [add_comm] using P.shift_add h.toAdd g.toAdd x)
        · exact (by simpa [add_comm] using P.shift_add h.toAdd g.toAdd y)
    ⟩
  letI : MulAction (Multiplicative (Site 2)) (Sym2 V) := ⟨by
    intro e
    change Sym2.map (P.shift (1 : Multiplicative (Site 2)).toAdd) e = e
    induction e using Sym2.inductionOn with
    | _ x y => simp [P.shift_zero]
    ⟩
  have htranslate (z : Site 2) :
      P.configTranslate z = ConfigSpace.shift (Multiplicative.ofAdd z) := by
    funext omega e
    induction e using Sym2.inductionOn with
    | _ x y => rfl
  have hTIstd : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu := by
    intro g
    have ht := htranslate g.toAdd
    change P.configTranslate g.toAdd = ConfigSpace.shift g at ht
    rw [← ht]
    exact hTI g.toAdd
  have hinvStd : ∀ g : Multiplicative (Site 2),
      ConfigSpace.shift g ⁻¹' s = s := by
    intro g
    have ht := htranslate g.toAdd
    change P.configTranslate g.toAdd = ConfigSpace.shift g at ht
    rw [← ht]
    exact hinv g.toAdd
  have hescape : ∀ (F : Finset (Sym2 V)) (k : ℕ),
      ∃ g : Multiplicative (Site 2),
        (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 V)) ⊆
          (P.bufferedEdgeWindow k)ᶜ := by
    intro F k
    exact E.bufferedEdgeWindow_escape F k
  obtain ⟨t, ht, hae⟩ := ati_invariant_aeTail P.bufferedEdgeWindow
    P.bufferedEdgeWindow_mono hescape hTIstd s hs hinvStd
  have heq : mu s = mu t := measure_congr hae
  rcases P.freeBufferedInfiniteVolume_tail_trivial hp hp1 hq t ht with ht0 | ht1
  · exact Or.inl (heq.trans ht0)
  · exact Or.inr (heq.trans ht1)

end PeriodicPlanar
end FK
end StatMech
