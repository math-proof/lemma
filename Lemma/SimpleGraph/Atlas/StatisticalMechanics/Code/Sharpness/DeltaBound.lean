import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.DeltaBound
open SimpleGraph Finset Classical StatMech StatMech.Sharpness


/--
[summable_gatedSourcePairSummand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma summable_gatedSourcePairSummand_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
-- given
  (P : Current V → Prop) :
-- imply
  Summable (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) => (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) * (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) * (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)) := by
-- proof
  apply StatMech.Sharpness.summable_gatedSourcePairSummand G β J A B P

/--
[gatedSourcePairSum_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma gatedSourcePairSum_partition_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
  {f : Current V → Finset V}
-- given
  (P : Current V → Prop) :
-- imply
  gatedSourcePairSum G β J A B P = ∑ S : Finset V, gatedSourcePairSum G β J A B (fun m => f m = S ∧ P m) := by
-- proof
  apply StatMech.Sharpness.gatedSourcePairSum_partition G β J A B P f

/--
[gatedSourcePairSum_congr_sources](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma gatedSourcePairSum_congr_sources_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {A B : Finset V}
  [DecidablePred P]
  [DecidablePred Q]
-- given
  (P Q : Current V → Prop)
  (h : ∀ p q : ↥G.edgeFinset → ℕ, sources G (ofEdgeFun G p) = A → sources G (ofEdgeFun G q) = B → (P (ofEdgeFun G (fun e => p e + q e)) ↔ Q (ofEdgeFun G (fun e => p e + q e)))) :
-- imply
  gatedSourcePairSum G β J A B P = gatedSourcePairSum G β J A B Q := by
-- proof
  apply StatMech.Sharpness.gatedSourcePairSum_congr_sources G β J A B P Q h

/--
[currentConnected_of_sources_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma currentConnected_of_sources_pair_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {u v : V}
-- given
  (huv : u ≠ v)
  (hsrc : sources G (ofEdgeFun G m) = {u, v}) :
-- imply
  CurrentConnected G (ofEdgeFun G m) u v := by
-- proof
  apply StatMech.Sharpness.currentConnected_of_sources_pair G m huv hsrc

/--
[current_disconnect_dichotomy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma current_disconnect_dichotomy_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : ↥G.edgeFinset → ℕ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hsrc : sources G (ofEdgeFun G m) = {o, x, y, g})
  (hng : ¬ CurrentConnected G (ofEdgeFun G m) o g) :
-- imply
  (CurrentConnected G (ofEdgeFun G m) o x ∧ CurrentConnected G (ofEdgeFun G m) y g) ∨ (CurrentConnected G (ofEdgeFun G m) o y ∧ CurrentConnected G (ofEdgeFun G m) x g) := by
-- proof
  apply StatMech.Sharpness.current_disconnect_dichotomy G m hox hoy hog hxy hxg hyg hsrc hng

/--
[deltaSource_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma deltaSource_comm_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  (({o, g} : Finset V) ∆ {x, y}) = ({y, g} : Finset V) ∆ {o, x} := by
-- proof
  apply StatMech.Sharpness.deltaSource_comm G hox hoy hog hxy hxg hyg

/--
[deltaSource_eq_four](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma deltaSource_eq_four_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  (({o, g} : Finset V) ∆ {x, y}) = {o, x, y, g} := by
-- proof
  apply StatMech.Sharpness.deltaSource_eq_four G hox hoy hog hxy hxg hyg

/--
[deltaEvent_notConnComp_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma deltaEvent_notConnComp_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y g : V}
  {S : Finset V}
  {p q : ↥G.edgeFinset → ℕ}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hp : sources G (ofEdgeFun G p) = ({o, g} : Finset V) ∆ {x, y})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  (notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o x ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔ (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧ notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S := by
-- proof
  apply StatMech.Sharpness.deltaEvent_notConnComp_iff G hox hoy hog hxy hxg hyg S p q hp hq

/--
[middleEvent_notConnComp_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma middleEvent_notConnComp_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y g : V}
  {S : Finset V}
  {p q : ↥G.edgeFinset → ℕ}
-- given
  (hox : o ≠ x)
  (hp : sources G (ofEdgeFun G p) = {o, x})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  (notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔ (o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S) ∧ notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S := by
-- proof
  apply StatMech.Sharpness.middleEvent_notConnComp_iff G hox S p q hp hq

/--
[middleEvent_notConnCompO_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma middleEvent_notConnCompO_iff_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o x y g : V}
  {S : Finset V}
  {p q : ↥G.edgeFinset → ℕ}
-- given
  (hox : o ≠ x)
  (hp : sources G (ofEdgeFun G p) = {o, x})
  (hq : sources G (ofEdgeFun G q) = ∅) :
-- imply
  (notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧ ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔ (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧ notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g := by
-- proof
  apply StatMech.Sharpness.middleEvent_notConnCompO_iff G hox S p q hp hq

/--
[sourcePairDisconn_eq_deltaPair_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma sourcePairDisconn_eq_deltaPair_add_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  sourcePairDisconnSum G β J {o, x, y, g} ∅ o g = isingDeltaPairSum G β J o x y g + isingDeltaPairSum G β J o y x g := by
-- proof
  apply StatMech.Sharpness.sourcePairDisconn_eq_deltaPair_add G β J hox hoy hog hxy hxg hyg

/--
[isingDeltaPairSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma isingDeltaPairSum_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  0 ≤ isingDeltaPairSum G β J o x y g := by
-- proof
  apply StatMech.Sharpness.isingDeltaPairSum_nonneg G β J hβ hJ o x y g

/--
[isingDeltaPairSum_partition_o](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma isingDeltaPairSum_partition_o_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  isingDeltaPairSum G β J o x y g = ∑ S : Finset V, if y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S then gatedSourcePairSum G β J (({o, g} : Finset V) ∆ {x, y}) ∅ (fun m => notConnComp G m o = S) else 0 := by
-- proof
  apply StatMech.Sharpness.isingDeltaPairSum_partition_o G β J hox hoy hog hxy hxg hyg

/--
[middlePairSum_partition_o](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma middlePairSum_partition_o_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x) :
-- imply
  gatedSourcePairSum G β J {o, x} ∅ (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) = ∑ S : Finset V, if y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S then gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m o = S ∧ CurrentConnected G m y g) else 0 := by
-- proof
  apply StatMech.Sharpness.middlePairSum_partition_o G β J hox

/--
[middlePairSum_partition_g](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma middlePairSum_partition_g_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hox : o ≠ x) :
-- imply
  gatedSourcePairSum G β J {o, x} ∅ (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) = ∑ S : Finset V, if o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S then gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m g = S) else 0 := by
-- proof
  apply StatMech.Sharpness.middlePairSum_partition_g G β J hox

/--
[claim2_ising_gated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma claim2_ising_gated_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {S : Finset V}
  {g o x : V}
-- given
  (hg : g ∉ S)
  (ho : o ∈ S)
  (hx : x ∈ S) :
-- imply
  gatedSourcePairSum G β J {o, x} ∅ (fun m => notConnComp G m g = S) = expectationJ G β (couplingIn J S) {o, x} * gatedSourcePairSum G β J ∅ ∅ (fun m => notConnComp G m g = S) := by
-- proof
  apply StatMech.Sharpness.claim2_ising_gated G β J S g o x hg ho hx

/--
[sourcePairDisconn_partition_o_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma sourcePairDisconn_partition_o_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o y g : V}
-- given
  (hyg : y ≠ g) :
-- imply
  sourcePairDisconnSum G β J {y, g} ∅ o g = ∑ S : Finset V, if y ∈ S ∧ g ∈ S ∧ o ∉ S then gatedSourcePairSum G β J {y, g} ∅ (fun m => notConnComp G m o = S) else 0 := by
-- proof
  apply StatMech.Sharpness.sourcePairDisconn_partition_o_self G β J hyg

/--
[middlePairSum_partition_g_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma middlePairSum_partition_g_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o y g : V} :
-- imply
  gatedSourcePairSum G β J ∅ ∅ (fun m => CurrentConnected G m y g ∧ ¬ CurrentConnected G m o g) = isingDeltaSelfLowerMass G β J o y g := by
-- proof
  apply StatMech.Sharpness.middlePairSum_partition_g_self G β J o y g

/--
[ising_delta_bound_cleared_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma ising_delta_bound_cleared_self_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hyg : y ≠ g) :
-- imply
  expectationJ G β J {y, g} * sourcePairDisconnSum G β J {y, g} ∅ o g ≥ isingDeltaSelfLowerMass G β J o y g := by
-- proof
  apply StatMech.Sharpness.ising_delta_bound_cleared_self G β J hβ hJ hyg

/--
[ising_delta_bound_cleared](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma ising_delta_bound_cleared_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g) :
-- imply
  expectationJ G β J {y, g} * isingDeltaPairSum G β J o x y g ≥ isingDeltaLowerMass G β J o x y g := by
-- proof
  apply StatMech.Sharpness.ising_delta_bound_cleared G β J hβ hJ hox hoy hog hxy hxg hyg

/--
[ising_delta_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean)
-/
@[path]
private lemma ising_delta_bound_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {o x y g : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hog : o ≠ g)
  (hxy : x ≠ y)
  (hxg : x ≠ g)
  (hyg : y ≠ g)
  (hmy : 0 < expectationJ G β J {y, g}) :
-- imply
  isingDeltaPairSum G β J o x y g ≥ (expectationJ G β J {y, g})⁻¹ * isingDeltaLowerMass G β J o x y g := by
-- proof
  apply StatMech.Sharpness.ising_delta_bound G β J hβ hJ hox hoy hog hxy hxg hyg hmy


-- created on 2026-10-23
