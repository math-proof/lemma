/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.IsingFK.EsWired.Part11
import Theorem.StatisticalMechanics.Code.IsingFK.EsLatticeBridge
import Theorem.StatisticalMechanics.Code.IsingFK.FvES.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Foundations.Prokhorov
import Def.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part7
open MeasureTheory Filter Topology TopologicalSpace
open scoped BigOperators ENNReal


namespace StatMech

namespace FK

open Lattice


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem freePottsJointFiniteMeasure_map_fst (d n q : ℕ) [NeZero q]
    (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (freePottsJointFiniteMeasure d n q beta J hp hp1).map
        continuous_fst.measurable.aemeasurable =
      freePottsFiniteMeasure d n q beta J := by
  ext s hs
  change (((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendJoint d n q)).map Prod.fst) s = _
  rw [Measure.map_map continuous_fst.measurable (ivp_measurable_extendJoint d n q)]
  change ((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendSpin d n q ∘ Prod.fst)) s = _
  have hfst : Measurable (Prod.fst :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (ivp_measurable_extendSpin d n q) hfst]
  rw [show Measure.map Prod.fst
      (ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure =
      ((ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.fst).toMeasure from
        PMF.toMeasure_map Prod.fst _ hfst,
    ivp_freeJointPMF_map_fst]
  rfl


theorem freePottsJointFiniteMeasure_map_snd (d n q : ℕ) [NeZero q]
    (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (freePottsJointFiniteMeasure d n q beta J hp hp1).map
        continuous_snd.measurable.aemeasurable =
      freeFiniteMeasure d n hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
  ext s hs
  change (((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (ivp_extendJoint d n q)).map Prod.snd) s = _
  rw [Measure.map_map continuous_snd.measurable (ivp_measurable_extendJoint d n q)]
  change ((ivp_freeJointPMF (boxGraph d n) q hp hp1
      (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure.map
        (extendEdge d n ∘ Prod.snd)) s = _
  have hsnd : Measurable (Prod.snd :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (measurable_extendEdge d n) hsnd]
  rw [show Measure.map Prod.snd
      (ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).toMeasure =
      ((ivp_freeJointPMF (boxGraph d n) q hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q)).map Prod.snd).toMeasure from
        PMF.toMeasure_map Prod.snd _ hsnd,
    ivp_freeJointPMF_map_snd]
  rfl


theorem wiredPottsJointFiniteMeasure_map_fst (d n q : ℕ) [NeZero q]
    (b : Fin q) (beta J : ℝ)
    (hp : 0 ≤ 1 - Real.exp (-(beta * J))) :
    (wiredPottsJointFiniteMeasure d n q b beta J hp).map
        continuous_fst.measurable.aemeasurable =
      wiredPottsFiniteMeasure d n q b beta J := by
  ext s hs
  change (((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp).toMeasure.map (ivp_extendJoint d n q)).map Prod.fst) s = _
  rw [Measure.map_map continuous_fst.measurable (ivp_measurable_extendJoint d n q)]
  change ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp).toMeasure.map (ivp_extendSpin d n q ∘ Prod.fst)) s = _
  have hfst : Measurable (Prod.fst :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (ivp_measurable_extendSpin d n q) hfst]
  rw [show Measure.map Prod.fst
      (Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp).toMeasure =
      ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp).map Prod.fst).toMeasure from PMF.toMeasure_map Prod.fst _ hfst,
    Wired.ivp_wiredJointPMF_map_fst]
  rfl


theorem wiredPottsJointFiniteMeasure_map_snd (d n q : ℕ) [NeZero q]
    (hd : 1 ≤ d) (hn : 1 ≤ n) (b : Fin q) (beta J : ℝ)
    (hp : 0 < 1 - Real.exp (-(beta * J)))
    (hp1 : 1 - Real.exp (-(beta * J)) < 1) :
    (wiredPottsJointFiniteMeasure d n q b beta J hp.le).map
        continuous_snd.measurable.aemeasurable =
      wiredFiniteMeasure d n hp hp1
        (by exact_mod_cast (Nat.pos_of_neZero q) : (0 : ℝ) < q) := by
  obtain ⟨v0, hv0⟩ := IsingFK.boxBoundary_nonempty d n hd hn
  ext s hs
  change (((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp.le).toMeasure.map (ivp_extendJoint d n q)).map Prod.snd) s = _
  rw [Measure.map_map continuous_snd.measurable (ivp_measurable_extendJoint d n q)]
  change ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
      b beta J hp.le).toMeasure.map (extendEdge d n ∘ Prod.snd)) s = _
  have hsnd : Measurable (Prod.snd :
      ((boxVerts d n → Fin q) × ConfigSpace (Sym2 (boxVerts d n))) → _) :=
    Measurable.of_discrete
  rw [← Measure.map_map (measurable_extendEdge d n) hsnd]
  rw [show Measure.map Prod.snd
      (Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp.le).toMeasure =
      ((Wired.ivp_wiredJointPMF (boxGraph d n) (boxBoundary d n)
        b beta J hp.le).map Prod.snd).toMeasure from PMF.toMeasure_map Prod.snd _ hsnd,
    Wired.ivp_wiredJointPMF_map_snd (boxGraph d n) (boxBoundary d n)
      b beta J hp hp1 v0 hv0]
  rfl


theorem freePottsInfiniteVolume_exists (d q : ℕ) [NeZero q] (hq : 2 ≤ q)
    (beta J : ℝ) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q))
      (mu : ProbabilityMeasure (PottsConfig d q)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      Tendsto (fun n => freePottsJointFiniteMeasure d (phi n) q beta J
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by
            have he := Real.exp_pos (-(beta * J))
            linarith))
        atTop (nhds Xi) ∧
      Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
        atTop (nhds mu) ∧
      Xi.map continuous_fst.measurable.aemeasurable = mu ∧
      Xi.map continuous_snd.measurable.aemeasurable =
        freeInfiniteVolume d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by
            have he := Real.exp_pos (-(beta * J))
            linarith)
          (by exact_mod_cast (show 0 < q by omega) : (0 : ℝ) < q) := by
  let p : ℝ := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    unfold p
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨psi, hpsi, hfk⟩ := freeInfiniteVolume_isLimit d hp hp1 hqR
  obtain ⟨Xi, eta, heta, hjoint0⟩ := probabilityMeasure_seq_compact
    (fun n => freePottsJointFiniteMeasure d (psi n) q beta J hp hp1)
  let phi : ℕ → ℕ := psi ∘ eta
  let mu : ProbabilityMeasure (PottsConfig d q) :=
    Xi.map continuous_fst.measurable.aemeasurable
  have hphi : StrictMono phi := hpsi.comp heta
  have hjoint : Tendsto
      (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
      atTop (nhds Xi) := by
    simpa [phi, Function.comp_def] using hjoint0
  have hspin0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi hjoint continuous_fst
  have hspin : Tendsto (fun n => freePottsFiniteMeasure d (phi n) q beta J)
      atTop (nhds mu) := by
    simpa only [freePottsJointFiniteMeasure_map_fst] using hspin0
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => freePottsJointFiniteMeasure d (phi n) q beta J hp hp1)
    Xi hjoint continuous_snd
  have hedge : Tendsto (fun n => freeFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (Xi.map continuous_snd.measurable.aemeasurable)) := by
    simpa only [freePottsJointFiniteMeasure_map_snd] using hedge0
  have hfk' : Tendsto (fun n => freeFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (freeInfiniteVolume d hp hp1 hqR)) := by
    simpa [phi, Function.comp_def] using hfk.comp heta.tendsto_atTop
  have hedgeEq : Xi.map continuous_snd.measurable.aemeasurable =
      freeInfiniteVolume d hp hp1 hqR :=
    tendsto_nhds_unique hedge hfk'
  refine ⟨Xi, mu, phi, hphi, ?_, hspin, rfl, hedgeEq⟩
  simpa [p] using hjoint


theorem wiredPottsInfiniteVolume_exists (d q : ℕ) [NeZero q]
    (hd : 1 ≤ d) (hq : 2 ≤ q)
    (b : Fin q) (beta J : ℝ) (hbeta : 0 < beta) (hJ : 0 < J) :
    ∃ (Xi : ProbabilityMeasure (PottsJointConfig d q))
      (mu : ProbabilityMeasure (PottsConfig d q)) (phi : ℕ → ℕ),
      StrictMono phi ∧
      Tendsto (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J
          (by
            apply sub_nonneg.mpr
            rw [Real.exp_le_one_iff]
            exact neg_nonpos.mpr (mul_pos hbeta hJ).le))
        atTop (nhds Xi) ∧
      Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
        atTop (nhds mu) ∧
      Xi.map continuous_fst.measurable.aemeasurable = mu ∧
      Xi.map continuous_snd.measurable.aemeasurable =
        wiredInfiniteVolume d
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            exact neg_neg_of_pos (mul_pos hbeta hJ))
          (by
            have he := Real.exp_pos (-(beta * J))
            linarith)
          (by exact_mod_cast (show 0 < q by omega) : (0 : ℝ) < q) := by
  let p : ℝ := 1 - Real.exp (-(beta * J))
  have hp : 0 < p := by
    unfold p
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos hbeta hJ)
  have hp1 : p < 1 := by
    unfold p
    linarith [Real.exp_pos (-(beta * J))]
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  obtain ⟨psi, hpsi, hfk⟩ := wiredInfiniteVolume_isLimit d hp hp1 hqR
  let rho : ℕ → ℕ := fun n => psi (n + 1)
  have hrho : StrictMono rho :=
    hpsi.comp (strictMono_nat_of_lt_succ fun n => by omega)
  have hrho_pos : ∀ n, 1 ≤ rho n := by
    intro n
    have hle : n + 1 ≤ psi (n + 1) := hpsi.id_le (n + 1)
    change 1 ≤ psi (n + 1)
    omega
  have hfkRho : Tendsto (fun n => wiredFiniteMeasure d (rho n) hp hp1 hqR)
      atTop (nhds (wiredInfiniteVolume d hp hp1 hqR)) := by
    simpa [rho, Function.comp_def] using hfk.comp (tendsto_add_atTop_nat 1)
  obtain ⟨Xi, eta, heta, hjoint0⟩ := probabilityMeasure_seq_compact
    (fun n => wiredPottsJointFiniteMeasure d (rho n) q b beta J hp.le)
  let phi : ℕ → ℕ := rho ∘ eta
  let mu : ProbabilityMeasure (PottsConfig d q) :=
    Xi.map continuous_fst.measurable.aemeasurable
  have hphi : StrictMono phi := hrho.comp heta
  have hjoint : Tendsto
      (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le)
      atTop (nhds Xi) := by
    simpa [phi, Function.comp_def] using hjoint0
  have hspin0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le)
    Xi hjoint continuous_fst
  have hspin : Tendsto (fun n => wiredPottsFiniteMeasure d (phi n) q b beta J)
      atTop (nhds mu) := by
    simpa only [wiredPottsJointFiniteMeasure_map_fst] using hspin0
  have hedge0 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le)
    Xi hjoint continuous_snd
  have hmapEdge : ∀ n,
      (wiredPottsJointFiniteMeasure d (phi n) q b beta J hp.le).map
          continuous_snd.measurable.aemeasurable =
        wiredFiniteMeasure d (phi n) hp hp1 hqR := by
    intro n
    exact wiredPottsJointFiniteMeasure_map_snd d (phi n) q hd
      (by simpa [phi] using hrho_pos (eta n)) b beta J hp hp1
  have hedge : Tendsto (fun n => wiredFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (Xi.map continuous_snd.measurable.aemeasurable)) := by
    simpa only [hmapEdge] using hedge0
  have hfk' : Tendsto (fun n => wiredFiniteMeasure d (phi n) hp hp1 hqR)
      atTop (nhds (wiredInfiniteVolume d hp hp1 hqR)) := by
    simpa [phi, Function.comp_def] using hfkRho.comp heta.tendsto_atTop
  have hedgeEq : Xi.map continuous_snd.measurable.aemeasurable =
      wiredInfiniteVolume d hp hp1 hqR :=
    tendsto_nhds_unique hedge hfk'
  refine ⟨Xi, mu, phi, hphi, ?_, hspin, rfl, hedgeEq⟩
  simpa [p] using hjoint

end FK
end StatMech
