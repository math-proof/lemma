import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.STTTransport.Part3
open SimpleGraph StatMech StatMech.Universality


/--
[bypass_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma bypass_vertex_eq
  {G1 G2 : SimpleGraph V}
  {O : V}
  {u v : V}
-- given
  (hedge : ∀ a b, a ≠ O → b ≠ O → G1.Adj a b → G2.Reachable a b)
  (hcorner : ∀ s t, s ≠ O → t ≠ O → G1.Adj s O → G1.Adj O t → G2.Reachable s t)
  (hu : u ≠ O)
  (hv : v ≠ O)
  (h : G1.Reachable u v) :
-- imply
  G2.Reachable u v := by
-- proof
  apply StatMech.Universality.bypass_vertex G1 G2 O hedge hcorner hu hv h

/--
[reach_collapse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma reach_collapse_eq
  {G1 G2 : SimpleGraph V}
  {ρ : V → V}
  {u v : V}
-- given
  (hcell : ∀ a b, G1.Adj a b → G2.Reachable (ρ a) (ρ b))
  (hu : ρ u = u)
  (hv : ρ v = v)
  (h : G1.Reachable u v) :
-- imply
  G2.Reachable u v := by
-- proof
  apply StatMech.Universality.reach_collapse G1 G2 ρ hcell hu hv h

/--
[triCell_adj_BC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_adj_BC_eq
  {A B C : V}
  {ω : LocalConfig}
-- given
  (h : ω.1 = true)
  (hBC : B ≠ C) :
-- imply
  (triCell A B C ω).Adj B C := by
-- proof
  apply StatMech.Universality.triCell_adj_BC A B C ω h hBC

/--
[triCell_adj_AC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_adj_AC_eq
  {A B C : V}
  {ω : LocalConfig}
-- given
  (h : ω.2.1 = true)
  (hAC : A ≠ C) :
-- imply
  (triCell A B C ω).Adj A C := by
-- proof
  apply StatMech.Universality.triCell_adj_AC A B C ω h hAC

/--
[triCell_adj_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_adj_AB_eq
  {A B C : V}
  {ω : LocalConfig}
-- given
  (h : ω.2.2 = true)
  (hAB : A ≠ B) :
-- imply
  (triCell A B C ω).Adj A B := by
-- proof
  apply StatMech.Universality.triCell_adj_AB A B C ω h hAB

/--
[triCell_adj_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_adj_imp_eq
  {A B C : V}
  {ω : LocalConfig}
  {x y : V}
-- given
  (h : (triCell A B C ω).Adj x y) :
-- imply
  (ω.1 ∧ s(x, y) = s(B, C)) ∨ (ω.2.1 ∧ s(x, y) = s(A, C)) ∨ (ω.2.2 ∧ s(x, y) = s(A, B)) := by
-- proof
  apply StatMech.Universality.triCell_adj_imp A B C ω h

/--
[starCell_adj_OA](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_adj_OA_eq
  {A B C O : V}
  {ω : LocalConfig}
-- given
  (h : ω.1 = true)
  (hOA : O ≠ A) :
-- imply
  (starCell A B C O ω).Adj O A := by
-- proof
  apply StatMech.Universality.starCell_adj_OA A B C O ω h hOA

/--
[starCell_adj_OB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_adj_OB_eq
  {A B C O : V}
  {ω : LocalConfig}
-- given
  (h : ω.2.1 = true)
  (hOB : O ≠ B) :
-- imply
  (starCell A B C O ω).Adj O B := by
-- proof
  apply StatMech.Universality.starCell_adj_OB A B C O ω h hOB

/--
[starCell_adj_OC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_adj_OC_eq
  {A B C O : V}
  {ω : LocalConfig}
-- given
  (h : ω.2.2 = true)
  (hOC : O ≠ C) :
-- imply
  (starCell A B C O ω).Adj O C := by
-- proof
  apply StatMech.Universality.starCell_adj_OC A B C O ω h hOC

/--
[starCell_adj_imp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_adj_imp_eq
  {A B C O : V}
  {ω : LocalConfig}
  {x y : V}
-- given
  (h : (starCell A B C O ω).Adj x y) :
-- imply
  (x = O ∧ ((y = A ∧ ω.1) ∨ (y = B ∧ ω.2.1) ∨ (y = C ∧ ω.2.2))) ∨ (y = O ∧ ((x = A ∧ ω.1) ∨ (x = B ∧ ω.2.1) ∨ (x = C ∧ ω.2.2))) := by
-- proof
  apply StatMech.Universality.starCell_adj_imp A B C O ω h

/--
[triCell_reach_BC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_reach_BC_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C : V}
  {ω : LocalConfig}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (h : triBC ω = true) :
-- imply
  (E ⊔ triCell A B C ω).Reachable B C := by
-- proof
  apply StatMech.Universality.triCell_reach_BC E A B C ω hAB hAC hBC h

/--
[triCell_reach_AC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_reach_AC_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C : V}
  {ω : LocalConfig}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (h : triAC ω = true) :
-- imply
  (E ⊔ triCell A B C ω).Reachable A C := by
-- proof
  apply StatMech.Universality.triCell_reach_AC E A B C ω hAB hAC hBC h

/--
[triCell_reach_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma triCell_reach_AB_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C : V}
  {ω : LocalConfig}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (h : triAB ω = true) :
-- imply
  (E ⊔ triCell A B C ω).Reachable A B := by
-- proof
  apply StatMech.Universality.triCell_reach_AB E A B C ω hAB hAC hBC h

/--
[starCell_reach_AB](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_reach_AB_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ω : LocalConfig}
-- given
  (hOA : O ≠ A)
  (hOB : O ≠ B)
  (h : starAB ω = true) :
-- imply
  (E ⊔ starCell A B C O ω).Reachable A B := by
-- proof
  apply StatMech.Universality.starCell_reach_AB E A B C O ω hOA hOB h

/--
[starCell_reach_AC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_reach_AC_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ω : LocalConfig}
-- given
  (hOA : O ≠ A)
  (hOC : O ≠ C)
  (h : starAC ω = true) :
-- imply
  (E ⊔ starCell A B C O ω).Reachable A C := by
-- proof
  apply StatMech.Universality.starCell_reach_AC E A B C O ω hOA hOC h

/--
[starCell_reach_BC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starCell_reach_BC_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ω : LocalConfig}
-- given
  (hOB : O ≠ B)
  (hOC : O ≠ C)
  (h : starBC ω = true) :
-- imply
  (E ⊔ starCell A B C O ω).Reachable B C := by
-- proof
  apply StatMech.Universality.starCell_reach_BC E A B C O ω hOB hOC h

/--
[reach_tri_to_star](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma reach_tri_to_star_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ωt ωs : LocalConfig}
  {u v : V}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (hOA : O ≠ A)
  (hOB : O ≠ B)
  (hOC : O ≠ C)
  (hm : MatchesPattern ωt ωs)
  (h : (E ⊔ triCell A B C ωt).Reachable u v) :
-- imply
  (E ⊔ starCell A B C O ωs).Reachable u v := by
-- proof
  apply StatMech.Universality.reach_tri_to_star E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm h

/--
[reach_star_to_tri](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma reach_star_to_tri_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ωt ωs : LocalConfig}
  {u v : V}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (hOA : O ≠ A)
  (hOB : O ≠ B)
  (hOC : O ≠ C)
  (hm : MatchesPattern ωt ωs)
  (hEO : ∀ x, ¬ E.Adj x O)
  (hu : u ≠ O)
  (hv : v ≠ O)
  (h : (E ⊔ starCell A B C O ωs).Reachable u v) :
-- imply
  (E ⊔ triCell A B C ωt).Reachable u v := by
-- proof
  apply StatMech.Universality.reach_star_to_tri E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv h

/--
[starTriangle_reach_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starTriangle_reach_iff_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ωt ωs : LocalConfig}
  {u v : V}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (hOA : O ≠ A)
  (hOB : O ≠ B)
  (hOC : O ≠ C)
  (hm : MatchesPattern ωt ωs)
  (hEO : ∀ x, ¬ E.Adj x O)
  (hu : u ≠ O)
  (hv : v ≠ O) :
-- imply
  (E ⊔ triCell A B C ωt).Reachable u v ↔ (E ⊔ starCell A B C O ωs).Reachable u v := by
-- proof
  apply StatMech.Universality.starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv

/--
[starTriangle_crossing_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STTTransport.lean)
-/
@[path]
private lemma starTriangle_crossing_transport_eq
  {E : SimpleGraph V}
  {A B C : V}
  {A B C O : V}
  {ωt ωs : LocalConfig}
  {u v : V}
-- given
  (hAB : A ≠ B)
  (hAC : A ≠ C)
  (hBC : B ≠ C)
  (hOA : O ≠ A)
  (hOB : O ≠ B)
  (hOC : O ≠ C)
  (hm : MatchesPattern ωt ωs)
  (hEO : ∀ x, ¬ E.Adj x O)
  (hu : u ≠ O)
  (hv : v ≠ O) :
-- imply
  (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ triCell A B C ωt).Reachable p q) ↔ (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ starCell A B C O ωs).Reachable p q) := by
-- proof
  apply StatMech.Universality.starTriangle_crossing_transport E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv


-- created on 2026-10-23
