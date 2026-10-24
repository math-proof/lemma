import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexWall3
open StatMech StatMech.Universality


/--
[hexWall3_mem_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_mem_reaches_eq
  {a : ℂ}
  {T : ℕ}
  {ts : List ℤ}
-- given
  (h0 : ℤ)
  (h : hexWall3_mem a h0 T ts) :
-- imply
  ∃ v ∈ (HexWalk.ofTurns a h0 ts).vertices, a.re + T ≤ v.re := by
-- proof
  apply StatMech.Universality.hexWall3_mem_reaches a h0 T ts h

/--
[hexWall3_column_colSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_column_colSum_eq
  {a : ℂ}
  {T : ℕ}
  {χ : ℝ}
  (hsummable hle_one)
  {y : ℝ}
-- given
  (h0 : ℤ) :
-- imply
  (hexWall3_column a h0 T χ hsummable hle_one).colSum y = ∑' w : {ts // hexWall3_mem a h0 T ts}, y ^ (HexWalk.ofTurns a h0 w.1).numVertices := by
-- proof
  apply StatMech.Universality.hexWall3_column_colSum a h0 T χ y

/--
[hexWall3_bridge_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_bridge_mem_eq
  {a : ℂ}
  {b : HexBridge}
-- given
  (h0 : ℤ)
  (hReaches : hexWall3_ReachesWidth a h0 b.width b.content)
  (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
-- imply
  hexWall3_mem a h0 b.width b.content := by
-- proof
  apply StatMech.Universality.hexWall3_bridge_mem a h0 b hReaches hSAW

/--
[hexWall3_colDomination_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_colDomination_uncond_eq
  {a : ℂ}
  {b : HexBridge}
  {χ : ℝ}
  (hsummable hle_one)
  {x : ℝ}
-- given
  (h0 : ℤ)
  (hx0 : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ)
  (hReaches : hexWall3_ReachesWidth a h0 b.width b.content)
  (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
-- imply
  x ^ (HexWalk.ofTurns a h0 b.content).numVertices ≤ (hexWall3_column a h0 b.width χ hsummable hle_one).colSum x := by
-- proof
  apply StatMech.Universality.hexWall3_colDomination_uncond a h0 b χ hx0 hχ hxχ hReaches hSAW

/--
[hexWall3_halfStep_re](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_halfStep_re_eq
-- given
  (h : ℤ) :
-- imply
  (HexWalk.halfStep h).re = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
-- proof
  apply StatMech.Universality.hexWall3_halfStep_re h

/--
[hexWall3_reachesWidth_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_reachesWidth_witness_eq
  {a : ℂ} :
-- imply
  hexWall3_ReachesWidth a 0 1 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexWall3_reachesWidth_witness a

/--
[hexWall3_isLegalSAW_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_isLegalSAW_witness_eq
  {a : ℂ} :
-- imply
  (HexWalk.ofTurns a 0 [(-1 : ℤ)]).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hexWall3_isLegalSAW_witness a

/--
[hexWall3_witness_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_witness_mem_eq
  {a : ℂ} :
-- imply
  hexWall3_mem a 0 1 [(-1 : ℤ)] := by
-- proof
  apply StatMech.Universality.hexWall3_witness_mem a

/--
[hexWall3_bridgeProd_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_bridgeProd_le_eq
  {bs : List HexBridge}
  {υ : ℕ → ℝ}
  {wtBr : HexBridge → ℝ}
-- given
  (h : StrictDecreasingWidths bs)
  (hdom : ∀ b ∈ bs, wtBr b ≤ υ b.width)
  (hwtnn : ∀ b ∈ bs, 0 ≤ wtBr b) :
-- imply
  (bs.map wtBr).prod ≤ ∏ T ∈ hbw_widthFinset bs, υ T := by
-- proof
  apply StatMech.Universality.hexWall3_bridgeProd_le bs h υ wtBr hdom hwtnn

/--
[hexWall3_weightBound_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hexWall3_weightBound_factor_eq
  {x g : ℝ}
  {lower upper : List HexBridge}
  {υ : ℕ → ℝ}
  {wtBr : HexBridge → ℝ}
-- given
  (hx : 0 < x)
  (hlo : StrictDecreasingWidths lower)
  (hup : StrictDecreasingWidths upper)
  (hdomLo : ∀ b ∈ lower, wtBr b ≤ υ b.width)
  (hdomUp : ∀ b ∈ upper, wtBr b ≤ υ b.width)
  (hwtnn : ∀ b, 0 ≤ wtBr b)
  (htwo : g * x ^ 2 = (lower.map wtBr).prod * (upper.map wtBr).prod) :
-- imply
  g ≤ (x ^ 2)⁻¹ * ((∏ T ∈ hbw_widthFinset lower, υ T) * (∏ T ∈ hbw_widthFinset upper, υ T)) := by
-- proof
  apply StatMech.Universality.hexWall3_weightBound_factor x g hx lower upper hlo hup υ wtBr hdomLo hdomUp hwtnn htwo

/--
[hex_connective_constant_2walls](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean)
-/
@[path]
private lemma hex_connective_constant_2walls_eq
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
  (hReachesLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d, hexWall3_ReachesWidth aB h0B b.width b.content)
  (hSAWLo : ∀ x hx hxlt N, ∀ d, ∀ b ∈ lower x hx hxlt N d, (HexWalk.ofTurns aB h0B b.content).IsLegalSAW)
  (hReachesUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d, hexWall3_ReachesWidth aB h0B b.width b.content)
  (hSAWUp : ∀ x hx hxlt N, ∀ d, ∀ b ∈ upper x hx hxlt N d, (HexWalk.ofTurns aB h0B b.content).IsLegalSAW) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hex_connective_constant_2walls c hge hsub a h0 B hFa hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc aB h0B hColsum hColle Dn Dn_fin wtγ wtγ_nn partial_eq lower upper hlo hup htwoEdge decomp_inj hReachesLo hSAWLo hReachesUp hSAWUp


-- created on 2026-10-23
