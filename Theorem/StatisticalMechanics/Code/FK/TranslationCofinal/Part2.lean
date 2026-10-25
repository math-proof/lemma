/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.TranslationInvariance.Part5
import Def.StatisticalMechanics.Code.FK.TranslationCofinal.Part2
open MeasureTheory Filter Topology SimpleGraph Set
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.IsingFK ConfigSpace

variable {d : ℕ}


theorem fktc_edgeIncl_boxEdge {N : ℕ} {x y : Site d} (hx : x ∈ box d N) (hy : y ∈ box d N) :
    edgeIncl d N (fktc_boxEdge hx hy) = s(x, y) := by
  unfold edgeIncl fktc_boxEdge
  rw [Sym2.map_mk]


theorem fktc_wired_density_eq_of_boxSym (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p :=
  fkTI_wired_density_shift_inv S N eb hp hp1


theorem fktc_free_density_eq_of_boxSym (S : BoxSym d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p :=
  fkTI_free_density_shift_inv S N eb hp hp1


theorem fktc_wired_box_density_const_of_orbit (S : BoxSym d) (N : ℕ)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    ∀ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  
  have hstep : ∀ k : ℕ, wiredEdgeDensity d 2 (edgeIncl d N ((Sym2.map (S.lift N))^[k] eb₀)) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply,
          ← fktc_wired_density_eq_of_boxSym S N ((Sym2.map (S.lift N))^[k] eb₀) hp hp1, ih]
  intro eb heb
  obtain ⟨k, hk⟩ := horb eb heb
  rw [hk, hstep k]


theorem fktc_free_box_density_const_of_orbit (S : BoxSym d) (N : ℕ)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    ∀ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hstep : ∀ k : ℕ, freeEdgeDensity d 2 (edgeIncl d N ((Sym2.map (S.lift N))^[k] eb₀)) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ', Function.comp_apply,
          ← fktc_free_density_eq_of_boxSym S N ((Sym2.map (S.lift N))^[k] eb₀) hp hp1, ih]
  intro eb heb
  obtain ⟨k, hk⟩ := horb eb heb
  rw [hk, hstep k]


theorem fktc_wired_density_eq_of_marg_decay (N : ℕ) (eb eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdecay : Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
  have hlim : wiredEdgeDensity d 2 (edgeIncl d N eb) p
      - wiredEdgeDensity d 2 (edgeIncl d N eb') p = 0 := by
    refine tendsto_nhds_unique
      ((dfi_wired_density_eq_limit N eb hp hp1).sub (dfi_wired_density_eq_limit N eb' hp hp1))
      hdecay
  linarith [hlim]


theorem fktc_free_density_eq_of_marg_decay (N : ℕ) (eb eb' : Sym2 (boxVerts d N))
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hdecay : Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb)
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) :
    freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb') p := by
  have hlim : freeEdgeDensity d 2 (edgeIncl d N eb) p
      - freeEdgeDensity d 2 (edgeIncl d N eb') p = 0 := by
    refine tendsto_nhds_unique
      ((dfi_free_density_eq_limit N eb hp hp1).sub (dfi_free_density_eq_limit N eb' hp hp1))
      hdecay
  linarith [hlim]


theorem fktc_wired_density_translation_inv (v x y : Site d) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hcof : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 s(x, y) p
      = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
  obtain ⟨N, hx, hy, hx', hy', hdecay⟩ := hcof
  have h1 : s(x, y) = edgeIncl d N (fktc_boxEdge hx hy) := (fktc_edgeIncl_boxEdge hx hy).symm
  have h2 : s(fktc_translate v x, fktc_translate v y)
      = edgeIncl d N (fktc_boxEdge hx' hy') := (fktc_edgeIncl_boxEdge hx' hy').symm
  rw [h1, h2]
  exact fktc_wired_density_eq_of_marg_decay N (fktc_boxEdge hx hy) (fktc_boxEdge hx' hy')
    hp hp1 hdecay


theorem fktc_free_density_translation_inv (v x y : Site d) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (hcof : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    freeEdgeDensity d 2 s(x, y) p
      = freeEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
  obtain ⟨N, hx, hy, hx', hy', hdecay⟩ := hcof
  have h1 : s(x, y) = edgeIncl d N (fktc_boxEdge hx hy) := (fktc_edgeIncl_boxEdge hx hy).symm
  have h2 : s(fktc_translate v x, fktc_translate v y)
      = edgeIncl d N (fktc_boxEdge hx' hy') := (fktc_edgeIncl_boxEdge hx' hy').symm
  rw [h1, h2]
  exact fktc_free_density_eq_of_marg_decay N (fktc_boxEdge hx hy) (fktc_boxEdge hx' hy')
    hp hp1 hdecay


theorem fktc_density_translation_inv (v x y : Site d) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hcofW : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0))
    (hcofF : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N,
        ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N,
      Tendsto (fun k =>
        edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy))
          - edgeMargProb (fkProb (boxGraph d (N+k)) p 2)
            (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
    wiredEdgeDensity d 2 s(x, y) p
        = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p
      ∧ freeEdgeDensity d 2 s(x, y) p
        = freeEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p :=
  ⟨fktc_wired_density_translation_inv v x y hp hp1 hcofW,
    fktc_free_density_translation_inv v x y hp hp1 hcofF⟩


theorem fktc_wired_density_eq_const (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p
      = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
  have hsum : (∑ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_wired N n hNn EB hp hp1


theorem fktc_free_density_eq_const (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hconst : ∀ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p
      = freeEdgeDensity d 2 (edgeIncl d N eb₀) p)
    (hp : 0 < p) (hp1 : p < 1) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
  have hsum : (∑ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p)
      = (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
  rw [← hsum]
  exact dfi_box_density_bound_free N n hNn EB hp hp1


theorem fktc_wired_density_eq_const_orbit (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p
      ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω :=
  fktc_wired_density_eq_const N n hNn EB eb₀
    (fktc_wired_box_density_const_of_orbit S N EB eb₀ hp hp1 horb) hp hp1


theorem fktc_free_density_eq_const_orbit (S : BoxSym d) (N n : ℕ) (hNn : N ≤ n)
    (EB : Finset (Sym2 (boxVerts d N))) (eb₀ : Sym2 (boxVerts d N)) {p : ℝ}
    (hp : 0 < p) (hp1 : p < 1)
    (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
    (∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω
            * fkProb (boxGraph d n) p 2 ω)
      ≤ (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p :=
  fktc_free_density_eq_const N n hNn EB eb₀
    (fktc_free_box_density_const_of_orbit S N EB eb₀ hp hp1 horb) hp hp1

end FK
end StatMech
