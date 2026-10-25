/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.RevealmentCrossBox.Part7
import Theorem.StatisticalMechanics.Code.OSSS.SharpnessFK
import Theorem.StatisticalMechanics.Code.Walls.oc_boxcrossingscalesum
import Theorem.StatisticalMechanics.Code.Walls.oc_boxobjects.Part2
import Def.StatisticalMechanics.Code.Walls.oc_core
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.DecisionTree

open StatMech.OSSS.Revealment

open StatMech.OSSS.RevealmentConstruction

open StatMech.Lattice

open scoped Classical

variable {E : Type*} [Fintype E] [DecidableEq E]


section Family

variable {d : ℕ}


theorem oc_perScaleRevealment {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (l : List E)
    (discF : ℕ → Finset (Site d))
    (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
    (k : ℕ) (e : E) :
    reveal ν (oc_clusterTree endU endV o n l discF k) e
      ≤ (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d k) then (1 : ℝ) else 0)
        + (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d k) then (1 : ℝ) else 0) :=
  reveal_crossTree_le_connected hν hinj hcoh hadj o (vertexBoundary d n) k l (discF k)
    (hdisc k) e


theorem oc_perScaleRevealment_family {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (l : List E)
    (discF : ℕ → Finset (Site d))
    (hdisc : ∀ k, ∀ x ∈ discF k, x ∈ vertexBoundary d k)
    {κ : Type*} (kscale : κ → ℕ) (k : κ) (e : E) :
    reveal ν (oc_clusterTree endU endV o n l discF (kscale k)) e
      ≤ (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endU e) (vertexBoundary d (kscale k))
            then (1 : ℝ) else 0)
        + (expect ν fun ω =>
            if ConnectedToSet d (liftCfg edge ω) (endV e) (vertexBoundary d (kscale k))
            then (1 : ℝ) else 0) :=
  oc_perScaleRevealment hν hinj hcoh hadj o n l discF hdisc (kscale k) e


theorem oc_familyTrees_compute
    {edge : E → Sym2 (Site d)} (hinj : Function.Injective edge)
    {endU endV : E → Site d} (hcoh : ∀ e, edge e = s(endU e, endV e))
    (hadj : ∀ e, (hypercubicLattice d).Adj (endU e) (endV e))
    (o : Site d) (n : ℕ) (l : List E) (hl : ∀ e, e ∈ l)
    (discF : ℕ → Finset (Site d)) (k : ℕ)
    (hk : 1 ≤ k) (hkn : k ≤ n) (ho : o ∈ box d (k - 1))
    (hBdisc : ∀ b ∈ vertexBoundary d k, b ∈ discF k) (hoB : o ∉ discF k)
    (ω : ConfigSpace E)
    [Decidable (ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n))] :
    (oc_clusterTree endU endV o n l discF k).evalR ω
      = if ConnectedToSet d (liftCfg edge ω) o (vertexBoundary d n) then (1 : ℝ) else 0 :=
  evalR_crossTree_connected hinj hcoh hadj k n hk hkn o ho l hl (discF k) hBdisc hoB ω

end Family


section Averaged

variable {d : ℕ}


theorem oc_familyAveraged_covLowerBound {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDnn : 0 ≤ D) (hsum : ∀ e, (∑ k, R k e) ≤ D) :
    (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) :=
  SharpnessFK.covSum_ge_of_indicator hν hA T hT R hreach c₀ hc₀nn hc₀ D hDnn hsum


theorem oc_familyAveraged_covLowerBound_div {ν : E → Bool → ℝ} (hν : IsProbWeight ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {κ : Type*} [Fintype κ] [Nonempty κ]
    (T : κ → DecisionTree E) (hT : ∀ k, (T k).evalR = A.indicator (fun _ => (1 : ℝ)))
    (R : κ → E → ℝ) (hreach : ∀ k e, reveal ν (T k) e ≤ R k e)
    (c₀ : ℝ) (hc₀nn : 0 ≤ c₀) (hc₀ : ∀ e, c₀ ≤ ν e true * ν e false)
    (D : ℝ) (hDpos : 0 < D) (hsum : ∀ e, (∑ k, R k e) ≤ D) :
    ((Fintype.card κ : ℝ) * c₀ / D)
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := by
  have hmain := oc_familyAveraged_covLowerBound hν hA T hT R hreach c₀ hc₀nn hc₀ D hDpos.le hsum
  rw [div_mul_eq_mul_div, div_le_iff₀ hDpos]
  calc (Fintype.card κ : ℝ) * c₀
        * (expect ν (A.indicator (fun _ => (1 : ℝ)))
            * (1 - expect ν (A.indicator (fun _ => (1 : ℝ)))))
      ≤ D * ∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ))) := hmain
    _ = (∑ e, cov ν (CovLowerBound.coordI e) (A.indicator (fun _ => (1 : ℝ)))) * D := by ring

end Averaged
end Walls
end StatMech
