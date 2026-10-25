/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexInfraReach.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Def.StatisticalMechanics.Code.Universality.HexW3Link.Part2


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


theorem hexW3_bridgeDecomp_isDispBridge (h0 : ℤ) (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊)
    (hD : ∀ b ∈ bridgeDecomp γ h, 0 ≤ hexInfra_disp h0 b.content) :
    ∀ b' ∈ hexW3_dispBridgeDecomp h0 γ h hPos, hexInfra_IsDispBridge h0 b' := by
  intro b' hb'
  simp only [hexW3_dispBridgeDecomp, List.mem_map, List.mem_attach, true_and] at hb'
  obtain ⟨b, rfl⟩ := hb'
  exact hexW3_anchor_isDispBridge h0 b.1 (hPos b.1 b.2) (hD b.1 b.2)


theorem hexW3_bridgeDecomp_reaches (a : ℂ) (h0 : ℤ) (γ : List (ℕ × ℤ)) (h : hexHW_WF γ)
    (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊)
    (hD : ∀ b ∈ bridgeDecomp γ h, 0 ≤ hexInfra_disp h0 b.content) :
    ∀ b' ∈ hexW3_dispBridgeDecomp h0 γ h hPos,
      hexWall3_ReachesWidth a h0 b'.width b'.content := fun b' hb' =>
  hexInfra_reachesWidth_of_dispBridge a h0 b'
    (hexW3_bridgeDecomp_isDispBridge h0 γ h hPos hD b' hb')


theorem hex_connective_constant_wall3closed
    (c : ℕ → ℝ)
    (hge : ∀ n, 1 ≤ c n) (hsub : Submultiplicative c)
    
    (a : ℕ → ℂ) (h0 : ℕ → ℤ)
    (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
    (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
    
    (hlamMono : ∀ v, 1 ≤ v → hexConnFinalLam B v ≤ hexConnFinalLam B (v + 1))
    (hυpos : ∀ v, 1 ≤ v → 0 < hexConnFinalUps B v)
    (hυnn : ∀ v, 0 ≤ hexConnFinalUps B v)
    (hτnn : ∀ v, 0 ≤ hexConnFinalTau B v)
    
    (Cut : ℕ → HexHighestCut hexChiE⁻¹)
    (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) =
      hexConnFinalLam B (v + 1) - hexConnFinalLam B v)
    (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hexConnFinalUps B (v + 1))
    
    {Iτ : Type} (Eτ : HexContourEmb ℕ Iτ)
    (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
    (hτdiv : (∃ v, 1 ≤ v ∧ 0 < hexConnFinalTau B v) → ¬ Summable Eτ.wtContour)
    {Iυ : Type} (Eυ : HexColumnEmb ℕ Iυ)
    (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
    (hEυc : Eυ.fiberSum = hexConnFinalUps B)
    
    (aB : ℂ) (h0B : ℤ)
    (hColsum : ∀ T, Summable (fun w : {ts // hexWall3_mem aB h0B T ts} =>
      hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices))
    (hColle : ∀ T, (∑' w : {ts // hexWall3_mem aB h0B T ts},
      hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices) ≤ 1)
    
    (Dn : ∀ x, 0 < x → x < hexChiE → ∀ N, Type)
    (Dn_fin : ∀ x hx hxlt N, Fintype (Dn x hx hxlt N))
    (wtγ : ∀ x hx hxlt N, Dn x hx hxlt N → ℝ)
    (wtγ_nn : ∀ x hx hxlt N, ∀ d, 0 ≤ wtγ x hx hxlt N d)
    (partial_eq : ∀ x hx hxlt N,
      (Finset.univ (α := Dn x hx hxlt N)).sum (wtγ x hx hxlt N)
        = ∑ n ∈ Finset.range N, c n * x ^ n)
    (lower upper : ∀ x hx hxlt N, Dn x hx hxlt N → List HexBridge)
    (hlo : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (lower x hx hxlt N d))
    (hup : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (upper x hx hxlt N d))
    (htwoEdge : ∀ x hx hxlt N, ∀ d, wtγ x hx hxlt N d * x ^ 2
        = ((lower x hx hxlt N d).map
              (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod
          * ((upper x hx hxlt N d).map
              (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod)
    (decomp_inj : ∀ x hx hxlt N, Function.Injective
      (fun d => (hbw_widthFinset (lower x hx hxlt N d),
                 hbw_widthFinset (upper x hx hxlt N d))))
    
    
    (hDispLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d,
      hexInfra_IsDispBridge h0B b)
    (hDispUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d,
      hexInfra_IsDispBridge h0B b)
    
    (hSAWLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d,
      (HexWalk.ofTurns aB h0B b.content).IsLegalSAW)
    (hSAWUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d,
      (HexWalk.ofTurns aB h0B b.content).IsLegalSAW) :
    ∃ kappa : ℝ, 0 < kappa ∧
      Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧
      kappa = Real.sqrt (2 + Real.sqrt 2) :=
  hex_connective_constant_2walls c hge hsub a h0 B hFa hlamMono hυpos hυnn hτnn
    Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc aB h0B hColsum hColle
    Dn Dn_fin wtγ wtγ_nn partial_eq lower upper hlo hup htwoEdge decomp_inj
    
    (fun x hx hxlt N d b hb =>
      hexInfra_reachesWidth_of_dispBridge aB h0B b (hDispLo x hx hxlt N d b hb))
    (hSAWLo)
    (fun x hx hxlt N d b hb =>
      hexInfra_reachesWidth_of_dispBridge aB h0B b (hDispUp x hx hxlt N d b hb))
    (hSAWUp)


end StatMech.Universality
