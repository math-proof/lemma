import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
open Finset StatMech StatMech.FrontierB


/--
[sum_edgeCoupling_bond_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma sum_edgeCoupling_bond_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V ≃ W}
  {E : Finset (Sym2 V)}
  {J : Sym2 W → ℝ}
  {omega : ConfigSpace W} :
-- imply
  (∑ e ∈ E, J (Sym2.map sigma e) * bond (isingCfgEquiv sigma omega) e) = ∑ f ∈ sym2FinsetImage sigma E, J f * bond omega f := by
-- proof
  apply StatMech.FrontierB.sum_edgeCoupling_bond_relabel sigma E J omega

/--
[wJ_sym2FinsetImage_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma wJ_sym2FinsetImage_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V ≃ W}
  {E : Finset (Sym2 V)}
  {J : Sym2 W → ℝ}
  {omega : ConfigSpace W}
-- given
  (hf : W → ℝ) :
-- imply
  wJ E (fun e => J (Sym2.map sigma e)) (fun x => hf (sigma x)) (isingCfgEquiv sigma omega) = wJ (sym2FinsetImage sigma E) J hf omega := by
-- proof
  apply StatMech.FrontierB.wJ_sym2FinsetImage_relabel sigma E J hf omega

/--
[ZJ_sym2FinsetImage_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma ZJ_sym2FinsetImage_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V ≃ W}
  {E : Finset (Sym2 V)}
  {J : Sym2 W → ℝ}
-- given
  (hf : W → ℝ) :
-- imply
  ZJ E (fun e => J (Sym2.map sigma e)) (fun x => hf (sigma x)) = ZJ (sym2FinsetImage sigma E) J hf := by
-- proof
  apply StatMech.FrontierB.ZJ_sym2FinsetImage_relabel sigma E J hf

/--
[spinProd_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma spinProd_isingCfgEquiv_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V ≃ W}
  {A : Finset V}
  {omega : ConfigSpace W} :
-- imply
  spinProd A (isingCfgEquiv sigma omega) = spinProd (A.map sigma.toEmbedding) omega := by
-- proof
  apply StatMech.FrontierB.spinProd_isingCfgEquiv sigma A omega

/--
[expJ_spinProd_sym2FinsetImage_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma expJ_spinProd_sym2FinsetImage_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {sigma : V ≃ W}
  {E : Finset (Sym2 V)}
  {J : Sym2 W → ℝ}
  {A : Finset V}
-- given
  (hf : W → ℝ) :
-- imply
  expJ E (fun e => J (Sym2.map sigma e)) (fun x => hf (sigma x)) (spinProd A) = expJ (sym2FinsetImage sigma E) J hf (spinProd (A.map sigma.toEmbedding)) := by
-- proof
  apply StatMech.FrontierB.expJ_spinProd_sym2FinsetImage_relabel sigma E J hf A

/--
[wJ_sym2FinsetInl_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma wJ_sym2FinsetInl_isolated_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype X]
  [DecidableEq X]
  {E : Finset (Sym2 X)}
  {J : Sym2 (X ⊕ Y) → ℝ}
  {s : ConfigSpace X}
  {t : ConfigSpace Y} :
-- imply
  wJ (sym2FinsetInl E) J (fun _ => 0) (isingSumConfigEquiv.symm (s, t)) = wJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) s := by
-- proof
  apply StatMech.FrontierB.wJ_sym2FinsetInl_isolated E J s t

/--
[expJ_spinProd_sym2FinsetInl_isolated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma expJ_spinProd_sym2FinsetInl_isolated_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype X]
  [DecidableEq X]
  {E : Finset (Sym2 X)}
  {J : Sym2 (X ⊕ Y) → ℝ}
  {A : Finset X} :
-- imply
  expJ (sym2FinsetInl E) J (fun _ => 0) (spinProd (A.map ⟨Sum.inl, Sum.inl_injective⟩)) = expJ E (fun e => J (Sym2.map Sum.inl e)) (fun _ => 0) (spinProd A) := by
-- proof
  apply StatMech.FrontierB.expJ_spinProd_sym2FinsetInl_isolated E J A

/--
[expJ_spinProd_induce_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean)
-/
@[path]
private lemma expJ_spinProd_induce_le_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype U]
  [DecidableEq U]
  [DecidablePred P]
  {E : Finset (Sym2 {x // P x})}
  {F : Finset (Sym2 U)}
  {J : Sym2 U → ℝ}
  {A : Finset {x // P x}}
-- given
  (P : U → Prop)
  (hsub : sym2FinsetImage (StatMech.FK.agl_sumEquiv P) (sym2FinsetInl (Y := {x // ¬P x}) E) ⊆ F)
  (hJ : ∀ e ∈ F, 0 ≤ J e)
  (hdiag : ∀ e ∈ F, ¬e.IsDiag) :
-- imply
  expJ E (fun e => J (Sym2.map Subtype.val e)) (fun _ => 0) (spinProd A) ≤ expJ F J (fun _ => 0) (spinProd (A.map (Function.Embedding.subtype P))) := by
-- proof
  apply StatMech.FrontierB.expJ_spinProd_induce_le P E F J hsub hJ hdiag A


-- created on 2026-10-23
