/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalWitnessStep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
open scoped BigOperators
open SimpleGraph


namespace StatMech.FK

noncomputable section

theorem ocd_condBcProb_innerEvent_eq_of_psiExt
    {Vin Vout : Type*}
    [Fintype Vin] [DecidableEq Vin]
    [Fintype Vout] [DecidableEq Vout]
    {Gin : SimpleGraph Vin} [DecidableRel Gin.Adj]
    {Gout : SimpleGraph Vout} [DecidableRel Gout.Adj]
    {iota : Vin → Vout} {bdryOut : Vout → Prop}
    [DecidablePred bdryOut]
    (hiota : Function.Injective iota)
    (hadj : ocd_AdjMatch Gin Gout iota)
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (psi : ConfigSpace (Sym2 Vout))
    (mu : ConfigSpace (Sym2 Vin) → Real)
    (hmu : ∀ omega,
      condBcProb Gout
          (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
          (ocd_innerEdgeFinset iota) psi (ocd_psiExt iota psi omega) =
        mu omega)
    (A : Set (ConfigSpace (Sym2 Vin))) :
    (∑ rho : ConfigSpace (Sym2 Vout),
        (ocd_innerRestrict iota ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          condBcProb Gout
            (StatMech.Lattice.boundaryCliqueGraph bdryOut) p q
            (ocd_innerEdgeFinset iota) psi rho) =
      ∑ omega : ConfigSpace (Sym2 Vin),
        A.indicator (fun _ => (1 : Real)) omega * mu omega := by
  rw [ocd_condBcProb_psiExt_sum_eq_inducedBox
    hiota hadj hp hp1 hq psi (ocd_innerRestrict iota ⁻¹' A)]
  have hpre : ocd_psiExt iota psi ⁻¹'
      (ocd_innerRestrict iota ⁻¹' A) = A := by
    ext omega
    simp only [Set.mem_preimage, ocd_innerRestrict_psiExt hiota]
  rw [hpre]
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  have hdm := ocd_condBcProb_psiExt_eq_bcProb
    (Gin := Gin) (Gout := Gout) (ιV := iota) (bdryOut := bdryOut)
    hiota hadj hp hp1 hq psi omega
  exact hdm.symm.trans (hmu omega)


theorem ocd_outsideGraph_congr_edges
    {Vin Vout : Type*}
    [Fintype Vin] [DecidableEq Vin]
    [Fintype Vout] [DecidableEq Vout]
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (iota : Vin → Vout) (bdryOut : Vout → Prop)
    [DecidablePred bdryOut]
    (psi psi' : ConfigSpace (Sym2 Vout))
    (h : ∀ x y, Gout.Adj x y → psi s(x, y) = psi' s(x, y)) :
    ocd_outsideGraph Gout iota bdryOut psi =
      ocd_outsideGraph Gout iota bdryOut psi' := by
  apply SimpleGraph.ext
  ext x y
  simp only [ocd_outsideGraph_adj]
  constructor
  · rintro (⟨hadj, hopen, hrange⟩ | hbdry)
    · exact Or.inl ⟨hadj, (h x y hadj).symm ▸ hopen, hrange⟩
    · exact Or.inr hbdry
  · rintro (⟨hadj, hopen, hrange⟩ | hbdry)
    · exact Or.inl ⟨hadj, h x y hadj ▸ hopen, hrange⟩
    · exact Or.inr hbdry


theorem ocd_inducedWiring_congr_edges
    {Vin Vout : Type*}
    [Fintype Vin] [DecidableEq Vin]
    [Fintype Vout] [DecidableEq Vout]
    (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]
    (iota : Vin → Vout) (bdryOut : Vout → Prop)
    [DecidablePred bdryOut]
    (psi psi' : ConfigSpace (Sym2 Vout))
    (h : ∀ x y, Gout.Adj x y → psi s(x, y) = psi' s(x, y)) :
    ocd_inducedWiring Gout iota bdryOut psi =
      ocd_inducedWiring Gout iota bdryOut psi' := by
  have hout := ocd_outsideGraph_congr_edges
    Gout iota bdryOut psi psi' h
  apply SimpleGraph.ext
  ext x y
  simp only [ocd_inducedWiring_adj]
  rw [hout]


theorem bcProb_event_fibre_eq_mass_mul_cond
    {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (F : Finset (Sym2 V)) (psi : ConfigSpace (Sym2 V))
    (A : Set (ConfigSpace (Sym2 V))) :
    (∑ rho ∈ condFibre F psi,
        A.indicator (fun _ => (1 : Real)) rho * bcProb G C p q rho) =
      (∑ sigma ∈ condFibre F psi, bcProb G C p q sigma) *
        (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
          condBcProb G C p q F psi rho) := by
  have hrestrict :
      (∑ rho, A.indicator (fun _ => (1 : Real)) rho *
          condBcProb G C p q F psi rho) =
        ∑ rho ∈ condFibre F psi,
          A.indicator (fun _ => (1 : Real)) rho *
            condBcProb G C p q F psi rho := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro rho _ hrho
    rw [mem_condFibre] at hrho
    unfold condBcProb
    rw [if_neg hrho, mul_zero]
  rw [hrestrict, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rho hrho
  rw [mem_condFibre] at hrho
  have hbc := bcProb_eq_fibreMass_mul_condBcProb
    G C hp hp1 hq F rho
  have hfib : condFibre F rho = condFibre F psi := by
    ext sigma
    rw [mem_condFibre, mem_condFibre,
      agreesOff_congr (agreesOff_symm hrho)]
  rw [hfib] at hbc
  have hcond : condBcProb G C p q F rho rho =
      condBcProb G C p q F psi rho :=
    ocd_condBcProb_congr_dom G C p q F rho psi rho
      (agreesOff_symm hrho)
  rw [hcond] at hbc
  rw [hbc]
  ring

end
end StatMech.FK
