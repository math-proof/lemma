import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicFiniteGhostComparison.Part3
open Finset SimpleGraph StatMech StatMech.Universality


/--
[isingFiniteGhostConductance_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostConductance_nonneg_eq
  {G : SimpleGraph V}
  {ghostRate : V → Real}
-- given
  (hrate : ∀ x, 0 ≤ ghostRate x) :
-- imply
  ∀ x y, 0 ≤ isingFiniteGhostConductance G ghostRate x y := by
-- proof
  apply StatMech.Universality.isingFiniteGhostConductance_nonneg G ghostRate hrate

/--
[isingFiniteGhostConductance_pos_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostConductance_pos_of_adj_eq
  {G : SimpleGraph V}
  {ghostRate : V → Real} :
-- imply
  ∀ ⦃x y⦄, (isingFiniteGhostGraph G ghostRate).Adj x y → 0 < isingFiniteGhostConductance G ghostRate x y := by
-- proof
  apply StatMech.Universality.isingFiniteGhostConductance_pos_of_adj G ghostRate

/--
[isingFiniteGhostGraph_reachable_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostGraph_reachable_boundary_eq
  {G : SimpleGraph V}
  {ghostRate : V → Real}
-- given
  (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b) :
-- imply
  ∀ x : Option V, ∃ b, isingFiniteGhostBoundary b ∧ (isingFiniteGhostGraph G ghostRate).Reachable x b := by
-- proof
  apply StatMech.Universality.isingFiniteGhostGraph_reachable_boundary G ghostRate hreach

/--
[isingFiniteGhostGraph_reachable_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostGraph_reachable_boundaryWith_eq
  {G : SimpleGraph V}
  {ghostRate : V → Real}
-- given
  (boundary : V → Prop)
  (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧ G.Reachable x b) :
-- imply
  ∀ x : Option V, ∃ b, isingFiniteGhostBoundaryWith boundary b ∧ (isingFiniteGhostGraph G ghostRate).Reachable x b := by
-- proof
  apply StatMech.Universality.isingFiniteGhostGraph_reachable_boundaryWith G ghostRate boundary hreach

/--
[isingFiniteGhostLaplacian_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostLaplacian_some_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {ghostValue : Real}
  {f : V → Real}
  {x : V} :
-- imply
  isingFiniteWeightedLaplacian (isingFiniteGhostConductance G ghostRate) (isingFiniteGhostExtension ghostValue f) (some x) = isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x) := by
-- proof
  apply StatMech.Universality.isingFiniteGhostLaplacian_some G ghostRate ghostValue f x

/--
[isingFiniteGhostExtension_subharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostExtension_subharmonicOn_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {ghostValue : Real}
  {f : V → Real}
-- given
  (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x)) :
-- imply
  IsingFiniteWeightedSubharmonicOn (isingFiniteGhostConductance G ghostRate) isingFiniteGhostBoundary (isingFiniteGhostExtension ghostValue f) := by
-- proof
  apply StatMech.Universality.isingFiniteGhostExtension_subharmonicOn G ghostRate ghostValue f hmodified

/--
[isingFiniteGhostExtension_superharmonicOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostExtension_superharmonicOn_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {ghostValue : Real}
  {f : V → Real}
-- given
  (hmodified : ∀ x, isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x) ≤ 0) :
-- imply
  IsingFiniteWeightedSuperharmonicOn (isingFiniteGhostConductance G ghostRate) isingFiniteGhostBoundary (isingFiniteGhostExtension ghostValue f) := by
-- proof
  apply StatMech.Universality.isingFiniteGhostExtension_superharmonicOn G ghostRate ghostValue f hmodified

/--
[isingFiniteGhostExtension_subharmonicOn_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostExtension_subharmonicOn_boundaryWith_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {ghostValue : Real}
  {f : V → Real}
-- given
  (boundary : V → Prop)
  (hmodified : ∀ x, ¬ boundary x → 0 ≤ isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x)) :
-- imply
  IsingFiniteWeightedSubharmonicOn (isingFiniteGhostConductance G ghostRate) (isingFiniteGhostBoundaryWith boundary) (isingFiniteGhostExtension ghostValue f) := by
-- proof
  apply StatMech.Universality.isingFiniteGhostExtension_subharmonicOn_boundaryWith G ghostRate boundary ghostValue f hmodified

/--
[isingFiniteGhostExtension_superharmonicOn_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhostExtension_superharmonicOn_boundaryWith_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {ghostValue : Real}
  {f : V → Real}
-- given
  (boundary : V → Prop)
  (hmodified : ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x) ≤ 0) :
-- imply
  IsingFiniteWeightedSuperharmonicOn (isingFiniteGhostConductance G ghostRate) (isingFiniteGhostBoundaryWith boundary) (isingFiniteGhostExtension ghostValue f) := by
-- proof
  apply StatMech.Universality.isingFiniteGhostExtension_superharmonicOn_boundaryWith G ghostRate boundary ghostValue f hmodified

/--
[isingFiniteGhost_subharmonic_le_ghostValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhost_subharmonic_le_ghostValue_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {f : V → Real}
  {c : Real}
-- given
  (hrate : ∀ x, 0 ≤ ghostRate x)
  (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b)
  (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x + ghostRate x * (c - f x)) :
-- imply
  ∀ x, f x ≤ c := by
-- proof
  apply StatMech.Universality.isingFiniteGhost_subharmonic_le_ghostValue G ghostRate f c hrate hreach hmodified

/--
[isingFiniteGhost_ghostValue_le_superharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhost_ghostValue_le_superharmonic_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {f : V → Real}
  {c : Real}
-- given
  (hrate : ∀ x, 0 ≤ ghostRate x)
  (hreach : ∀ x, ∃ b, 0 < ghostRate b ∧ G.Reachable x b)
  (hmodified : ∀ x, isingFiniteGraphLaplacian G f x + ghostRate x * (c - f x) ≤ 0) :
-- imply
  ∀ x, c ≤ f x := by
-- proof
  apply StatMech.Universality.isingFiniteGhost_ghostValue_le_superharmonic G ghostRate f c hrate hreach hmodified

/--
[isingFiniteGhost_subharmonic_le_const_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhost_subharmonic_le_const_boundaryWith_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {f : V → Real}
  {ghostValue c : Real}
-- given
  (boundary : V → Prop)
  (hrate : ∀ x, 0 ≤ ghostRate x)
  (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧ G.Reachable x b)
  (hmodified : ∀ x, ¬ boundary x → 0 ≤ isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x))
  (hghost : ghostValue ≤ c)
  (hboundary : ∀ x, boundary x → f x ≤ c) :
-- imply
  ∀ x, f x ≤ c := by
-- proof
  apply StatMech.Universality.isingFiniteGhost_subharmonic_le_const_boundaryWith G ghostRate boundary f ghostValue c hrate hreach hmodified hghost hboundary

/--
[isingFiniteGhost_const_le_superharmonic_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFiniteGhost_const_le_superharmonic_boundaryWith_eq
  [Fintype V]
  {G : SimpleGraph V}
  {ghostRate : V → Real}
  {f : V → Real}
  {ghostValue c : Real}
-- given
  (boundary : V → Prop)
  (hrate : ∀ x, 0 ≤ ghostRate x)
  (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < ghostRate b) ∧ G.Reachable x b)
  (hmodified : ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x + ghostRate x * (ghostValue - f x) ≤ 0)
  (hghost : c ≤ ghostValue)
  (hboundary : ∀ x, boundary x → c ≤ f x) :
-- imply
  ∀ x, c ≤ f x := by
-- proof
  apply StatMech.Universality.isingFiniteGhost_const_le_superharmonic_boundaryWith G ghostRate boundary f ghostValue c hrate hreach hmodified hghost hboundary

/--
[isingFermionicGhostCoefficient_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhostCoefficient_pos_eq :
-- imply
  0 < isingFermionicGhostCoefficient := by
-- proof
  apply StatMech.Universality.isingFermionicGhostCoefficient_pos

/--
[isingFermionicGhostRate_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhostRate_nonneg_eq
  {boundaryMultiplicity : V → Nat} :
-- imply
  ∀ x, 0 ≤ isingFermionicGhostRate boundaryMultiplicity x := by
-- proof
  apply StatMech.Universality.isingFermionicGhostRate_nonneg boundaryMultiplicity

/--
[isingFermionicGhostRate_pos_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhostRate_pos_iff_eq
  {boundaryMultiplicity : V → Nat}
  {x : V} :
-- imply
  0 < isingFermionicGhostRate boundaryMultiplicity x ↔ 0 < boundaryMultiplicity x := by
-- proof
  apply StatMech.Universality.isingFermionicGhostRate_pos_iff boundaryMultiplicity x

/--
[isingFermionicGhost_subharmonic_le_ghostValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhost_subharmonic_le_ghostValue_eq
  [Fintype V]
  {G : SimpleGraph V}
  {boundaryMultiplicity : V → Nat}
  {f : V → Real}
  {c : Real}
-- given
  (hreach : ∀ x, ∃ b, 0 < boundaryMultiplicity b ∧ G.Reachable x b)
  (hmodified : ∀ x, 0 ≤ isingFiniteGraphLaplacian G f x + isingFermionicGhostRate boundaryMultiplicity x * (c - f x)) :
-- imply
  ∀ x, f x ≤ c := by
-- proof
  apply StatMech.Universality.isingFermionicGhost_subharmonic_le_ghostValue G boundaryMultiplicity f c hreach hmodified

/--
[isingFermionicGhost_ghostValue_le_superharmonic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhost_ghostValue_le_superharmonic_eq
  [Fintype V]
  {G : SimpleGraph V}
  {boundaryMultiplicity : V → Nat}
  {f : V → Real}
  {c : Real}
-- given
  (hreach : ∀ x, ∃ b, 0 < boundaryMultiplicity b ∧ G.Reachable x b)
  (hmodified : ∀ x, isingFiniteGraphLaplacian G f x + isingFermionicGhostRate boundaryMultiplicity x * (c - f x) ≤ 0) :
-- imply
  ∀ x, c ≤ f x := by
-- proof
  apply StatMech.Universality.isingFermionicGhost_ghostValue_le_superharmonic G boundaryMultiplicity f c hreach hmodified

/--
[isingFermionicGhost_subharmonic_le_const_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhost_subharmonic_le_const_boundaryWith_eq
  [Fintype V]
  {G : SimpleGraph V}
  {boundaryMultiplicity : V → Nat}
  {f : V → Real}
  {ghostValue c : Real}
-- given
  (boundary : V → Prop)
  (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < boundaryMultiplicity b) ∧ G.Reachable x b)
  (hmodified : ∀ x, ¬ boundary x → 0 ≤ isingFiniteGraphLaplacian G f x + isingFermionicGhostRate boundaryMultiplicity x * (ghostValue - f x))
  (hghost : ghostValue ≤ c)
  (hboundary : ∀ x, boundary x → f x ≤ c) :
-- imply
  ∀ x, f x ≤ c := by
-- proof
  apply StatMech.Universality.isingFermionicGhost_subharmonic_le_const_boundaryWith G boundaryMultiplicity boundary f ghostValue c hreach hmodified hghost hboundary

/--
[isingFermionicGhost_const_le_superharmonic_boundaryWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicFiniteGhostComparison.lean)
-/
@[path]
private lemma isingFermionicGhost_const_le_superharmonic_boundaryWith_eq
  [Fintype V]
  {G : SimpleGraph V}
  {boundaryMultiplicity : V → Nat}
  {f : V → Real}
  {ghostValue c : Real}
-- given
  (boundary : V → Prop)
  (hreach : ∀ x, ∃ b, (boundary b ∨ 0 < boundaryMultiplicity b) ∧ G.Reachable x b)
  (hmodified : ∀ x, ¬ boundary x → isingFiniteGraphLaplacian G f x + isingFermionicGhostRate boundaryMultiplicity x * (ghostValue - f x) ≤ 0)
  (hghost : c ≤ ghostValue)
  (hboundary : ∀ x, boundary x → c ≤ f x) :
-- imply
  ∀ x, c ≤ f x := by
-- proof
  apply StatMech.Universality.isingFermionicGhost_const_le_superharmonic_boundaryWith G boundaryMultiplicity boundary f ghostValue c hreach hmodified hghost hboundary


-- created on 2026-10-23
