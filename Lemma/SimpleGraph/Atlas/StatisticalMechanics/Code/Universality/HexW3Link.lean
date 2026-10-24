import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexW3Link
open StatMech StatMech.Universality


/--
[hexW3_anchor_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_anchor_content_eq
  {b : HexBridge}
  (hpos)
-- given
  (h0 : ℤ) :
-- imply
  (hexW3_anchor h0 b hpos).content = b.content := by
-- proof
  apply StatMech.Universality.hexW3_anchor_content h0 b

/--
[hexW3_anchor_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_anchor_width_eq
  {b : HexBridge}
  (hpos)
-- given
  (h0 : ℤ) :
-- imply
  (hexW3_anchor h0 b hpos).width = ⌊hexInfra_disp h0 b.content⌋₊ := by
-- proof
  apply StatMech.Universality.hexW3_anchor_width h0 b

/--
[hexW3_anchor_isDispBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_anchor_isDispBridge_eq
  {b : HexBridge}
  (hpos)
-- given
  (h0 : ℤ)
  (hd : 0 ≤ hexInfra_disp h0 b.content) :
-- imply
  hexInfra_IsDispBridge h0 (hexW3_anchor h0 b hpos) := by
-- proof
  apply StatMech.Universality.hexW3_anchor_isDispBridge h0 b hd

/--
[hexW3_anchor_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_anchor_reaches_eq
  {a : ℂ}
  {b : HexBridge}
  (hpos)
-- given
  (h0 : ℤ)
  (hd : 0 ≤ hexInfra_disp h0 b.content) :
-- imply
  hexWall3_ReachesWidth a h0 (hexW3_anchor h0 b hpos).width (hexW3_anchor h0 b hpos).content := by
-- proof
  apply StatMech.Universality.hexW3_anchor_reaches a h0 b hd

/--
[hexW3_bridgeDecomp_isDispBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_bridgeDecomp_isDispBridge_eq
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ)
  (h : hexHW_WF γ)
  (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊)
  (hD : ∀ b ∈ bridgeDecomp γ h, 0 ≤ hexInfra_disp h0 b.content) :
-- imply
  ∀ b' ∈ hexW3_dispBridgeDecomp h0 γ h hPos, hexInfra_IsDispBridge h0 b' := by
-- proof
  apply StatMech.Universality.hexW3_bridgeDecomp_isDispBridge h0 γ h hPos hD

/--
[hexW3_bridgeDecomp_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_bridgeDecomp_reaches_eq
  {a : ℂ}
  {γ : List (ℕ × ℤ)}
-- given
  (h0 : ℤ)
  (h : hexHW_WF γ)
  (hPos : ∀ b ∈ bridgeDecomp γ h, 0 < ⌊hexInfra_disp h0 b.content⌋₊)
  (hD : ∀ b ∈ bridgeDecomp γ h, 0 ≤ hexInfra_disp h0 b.content) :
-- imply
  ∀ b' ∈ hexW3_dispBridgeDecomp h0 γ h hPos, hexWall3_ReachesWidth a h0 b'.width b'.content := by
-- proof
  apply StatMech.Universality.hexW3_bridgeDecomp_reaches a h0 γ h hPos hD

/--
[hex_connective_constant_wall3closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hex_connective_constant_wall3closed_eq
  {c : ℕ → ℝ}
  {a : ℕ → ℂ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
  {aB : ℂ}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c)
  (h0 : ℕ → ℤ)
  (B : ∀ v, HexBoundaryDecomp (hexUncondDomain (a v) (h0 v)) (hexUncondPairing (a v) (h0 v)))
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
  (hlamMono : ∀ v, 1 ≤ v → hexConnFinalLam B v ≤ hexConnFinalLam B (v + 1))
  (hυpos : ∀ v, 1 ≤ v → 0 < hexConnFinalUps B v)
  (hυnn : ∀ v, 0 ≤ hexConnFinalUps B v)
  (hτnn : ∀ v, 0 ≤ hexConnFinalTau B v)
  (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = hexConnFinalLam B (v + 1) - hexConnFinalLam B v)
  (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = hexConnFinalUps B (v + 1))
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < hexConnFinalTau B v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = hexConnFinalUps B)
  (h0B : ℤ)
  (hColsum : ∀ T, Summable (fun w : {ts // hexWall3_mem aB h0B T ts} => hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices))
  (hColle : ∀ T, (∑' w : {ts // hexWall3_mem aB h0B T ts}, hexChiE ^ (HexWalk.ofTurns aB h0B w.1).numVertices) ≤ 1)
  (Dn : ∀ x, 0 < x → x < hexChiE → ∀ N, Type)
  (Dn_fin : ∀ x hx hxlt N, Fintype (Dn x hx hxlt N))
  (wtγ : ∀ x hx hxlt N, Dn x hx hxlt N → ℝ)
  (wtγ_nn : ∀ x hx hxlt N, ∀ d, 0 ≤ wtγ x hx hxlt N d)
  (partial_eq : ∀ x hx hxlt N, (Finset.univ (α := Dn x hx hxlt N)).sum (wtγ x hx hxlt N) = ∑ n ∈ Finset.range N, c n * x ^ n)
  (lower upper : ∀ x hx hxlt N, Dn x hx hxlt N → List HexBridge)
  (hlo : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (lower x hx hxlt N d))
  (hup : ∀ x hx hxlt N, ∀ d, StrictDecreasingWidths (upper x hx hxlt N d))
  (htwoEdge : ∀ x hx hxlt N, ∀ d, wtγ x hx hxlt N d * x ^ 2 = ((lower x hx hxlt N d).map (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod * ((upper x hx hxlt N d).map (fun b => x ^ (HexWalk.ofTurns aB h0B b.content).numVertices)).prod)
  (decomp_inj : ∀ x hx hxlt N, Function.Injective (fun d => (hbw_widthFinset (lower x hx hxlt N d), hbw_widthFinset (upper x hx hxlt N d))))
  (hDispLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d, hexInfra_IsDispBridge h0B b)
  (hDispUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d, hexInfra_IsDispBridge h0B b)
  (hSAWLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d, (HexWalk.ofTurns aB h0B b.content).IsLegalSAW)
  (hSAWUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d, (HexWalk.ofTurns aB h0B b.content).IsLegalSAW) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hex_connective_constant_wall3closed c hge hsub a h0 B hFa hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc aB h0B hColsum hColle Dn Dn_fin wtγ wtγ_nn partial_eq lower upper hlo hup htwoEdge decomp_inj hDispLo hDispUp hSAWLo hSAWUp

/--
[hexW3_witnessBridge_content](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessBridge_content_eq :
-- imply
  hexW3_witnessBridge.content = [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexW3_witnessBridge_content

/--
[hexW3_witnessBridge_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessBridge_width_eq :
-- imply
  hexW3_witnessBridge.width = 1 := by
-- proof
  apply StatMech.Universality.hexW3_witnessBridge_width

/--
[hexW3_witness_isDispBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witness_isDispBridge_eq :
-- imply
  hexInfra_IsDispBridge 0 hexW3_witnessBridge := by
-- proof
  apply StatMech.Universality.hexW3_witness_isDispBridge

/--
[hexW3_witness_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witness_reaches_eq
  {a : ℂ} :
-- imply
  hexWall3_ReachesWidth a 0 hexW3_witnessBridge.width hexW3_witnessBridge.content := by
-- proof
  apply StatMech.Universality.hexW3_witness_reaches a

/--
[hexW3_witnessRung_wf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessRung_wf_eq :
-- imply
  hexHW_WF [((1 : ℕ), (-1 : ℤ))] := by
-- proof
  apply StatMech.Universality.hexW3_witnessRung_wf

/--
[hexW3_witnessRung_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessRung_decomp_eq :
-- imply
  bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf = [(⟨1, one_pos, [(-1 : ℤ)], by simp⟩ : HexBridge)] := by
-- proof
  apply StatMech.Universality.hexW3_witnessRung_decomp

/--
[hexW3_witnessRung_hPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessRung_hPos_eq :
-- imply
  ∀ b ∈ bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf, 0 < ⌊hexInfra_disp 0 b.content⌋₊ := by
-- proof
  apply StatMech.Universality.hexW3_witnessRung_hPos

/--
[hexW3_witnessRung_hD](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessRung_hD_eq :
-- imply
  ∀ b ∈ bridgeDecomp [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf, 0 ≤ hexInfra_disp 0 b.content := by
-- proof
  apply StatMech.Universality.hexW3_witnessRung_hD

/--
[hexW3_witnessRung_dispBridge_nonempty_anchored](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW3Link.lean)
-/
@[path]
private lemma hexW3_witnessRung_dispBridge_nonempty_anchored_eq :
-- imply
  (hexW3_dispBridgeDecomp 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf hexW3_witnessRung_hPos) ≠ [] ∧ ∀ b' ∈ hexW3_dispBridgeDecomp 0 [((1 : ℕ), (-1 : ℤ))] hexW3_witnessRung_wf hexW3_witnessRung_hPos, hexInfra_IsDispBridge 0 b' := by
-- proof
  apply StatMech.Universality.hexW3_witnessRung_dispBridge_nonempty_anchored


-- created on 2026-10-23
