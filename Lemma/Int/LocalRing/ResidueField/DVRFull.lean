import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.LocalRing.ResidueField.DVR.Part2
import Lemma.AlgHom.LocalRing.ResidueField.DVR


namespace DVRResidue

/--
[exists_root_lift_of_adjoin_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRFull.lean)
-/
@[path]
lemma exists_root_lift_of_adjoin_eq_top
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [HenselianLocalRing C]
  {beta : B}
  {f : IsLocalRing.ResidueField B →ₐ[IsLocalRing.ResidueField A] IsLocalRing.ResidueField C}
-- given
  (hbeta : Algebra.adjoin A {beta} = ⊤) :
-- imply
  exists gamma : C, Polynomial.aeval gamma (minpoly A beta) = 0 /\
    IsLocalRing.residue C gamma = f (IsLocalRing.residue B beta) := by
-- proof
  have hInt : IsIntegral A beta := Algebra.IsIntegral.isIntegral beta
  let q : Polynomial A := minpoly A beta
  let P : Polynomial C := q.map (algebraMap A C)
  let rB : IsLocalRing.ResidueField B := IsLocalRing.residue B beta
  let a0 : IsLocalRing.ResidueField C := f rB
  let : Module.Free A B := Module.free_of_flat_of_isLocalRing
  have hPmonic : P.Monic := (minpoly.monic hInt).map _
  have h2 := ((HenselianLocalRing.TFAE C).out 1 2).mp
    (inferInstance : HenselianLocalRing C)
  have hcomp : (IsLocalRing.residue C).comp (algebraMap A C) =
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)).comp
      (IsLocalRing.residue A) := by
    rw [show algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) =
      IsLocalRing.ResidueField.map (algebraMap A C) from rfl]
    exact (IsLocalRing.ResidueField.map_comp_residue (algebraMap A C)).symm
  have hred : P.map (IsLocalRing.residue C) =
    (minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C)) := by
    simp only [P, q, Polynomial.map_map]
    rw [hcomp, ← Polynomial.map_map, IsLocalRing.minpoly_map_residue hbeta]
  have hmin : Polynomial.aeval rB (minpoly (IsLocalRing.ResidueField A) rB) = 0 :=
    minpoly.aeval _ _
  have hrootB : ((minpoly (IsLocalRing.ResidueField A) rB).map
    (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B))).IsRoot rB := by
    rwa [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
  have hbase : f.toRingHom.comp
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) =
    algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField C) := by
    ext r
    exact f.commutes r
  have hmapEq : (((minpoly (IsLocalRing.ResidueField A) rB).map
    (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))).map
    f.toRingHom) =
    (minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField C)) := by
    rw [Polynomial.map_map, hbase]
  have hrootC' : ((minpoly (IsLocalRing.ResidueField A) rB).map
    (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C))).IsRoot a0 := by
    have h := hrootB.map (f := f.toRingHom)
    rw [hmapEq] at h
    change ((minpoly (IsLocalRing.ResidueField A) rB).map
      (algebraMap (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField C))).IsRoot (f.toRingHom rB)
    exact h
  have hP : (P.map (IsLocalRing.residue C)).IsRoot a0 := by
    rwa [hred]
  have hroot0 : Polynomial.aeval a0 P = 0 := by
    have hPeval : (P.map (IsLocalRing.residue C)).eval a0 = 0 :=
      Polynomial.IsRoot.def.mp hP
    rw [Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
      ← Polynomial.eval_map]
    exact hPeval
  have hsep : (minpoly (IsLocalRing.ResidueField A) rB).Separable :=
    Algebra.IsSeparable.isSeparable _ _
  have hsepC : ((minpoly (IsLocalRing.ResidueField A) rB).map
    (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField C))).Separable := by
    exact hsep.map
  have hsepP : (P.map (IsLocalRing.residue C)).Separable := by
    rwa [hred]
  have hP_aeval : Polynomial.aeval a0 (P.map (IsLocalRing.residue C)) = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.IsRoot.def] using hP
  have hne := hsepP.aeval_derivative_ne_zero hP_aeval
  have hderiv0 : Polynomial.aeval a0 P.derivative ≠ 0 := by
    simpa [Polynomial.aeval_def, IsLocalRing.ResidueField.algebraMap_eq,
      Polynomial.derivative_map, Polynomial.eval_map] using hne
  obtain ⟨gamma, hroot, hres⟩ := h2 P hPmonic a0 hroot0 hderiv0
  refine ⟨gamma, ?_, hres⟩
  simpa [P, Polynomial.IsRoot.def] using hroot

end DVRResidue

namespace DVRResidue

/--
[residueFieldMapAlgHom_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/LocalRing/ResidueField/DVRFull.lean)
-/
@[path]
lemma residueFieldMapAlgHom_surjective
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A B] [Algebra A C] [Module.Finite A B] [Module.Finite A C] [IsLocalHom (algebraMap A B)] [IsLocalHom (algebraMap A C)] [Algebra.Etale A B] [HenselianLocalRing C] :
-- imply
  Function.Surjective
    (residueFieldMapAlgHom (A := by
-- proof
  classical
  let : Module.Free A B := Module.free_of_flat_of_isLocalRing
  obtain ⟨beta, hbeta⟩ := IsLocalRing.exists_adjoin_eq_top (R := A) (S := B)
  intro f
  obtain ⟨gamma, hgamma, hres⟩ :=
    exists_root_lift_of_adjoin_eq_top hbeta f
  let hRoot := IsAdjoinRootMonic.mkOfAdjoinEqTop' hbeta
  let phi : B →ₐ[A] C := hRoot.liftHom gamma hgamma
  refine ⟨phi, ?_⟩
  refine AlgHom.ext_of_adjoin_eq_top
    ((IsLocalRing.adjoin_residue_eq_top_iff_adjoin_eq_top beta).mpr hbeta) ?_
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  change residueFieldMapAlgHom phi (IsLocalRing.residue B beta) = _
  rw [residueFieldMapAlgHom_residue]
  change IsLocalRing.residue C (hRoot.liftHom gamma hgamma beta) = _
  have hbetaRoot : hRoot.root = beta := by
    dsimp only [hRoot]
    exact IsAdjoinRootMonic.mkOfAdjoinEqTop'_root hbeta
  have hphiBeta : hRoot.liftHom gamma hgamma beta = gamma := by
    simpa only [hbetaRoot] using hRoot.liftHom_root hgamma
  rwa [hphiBeta]

end DVRResidue


-- created on 2026-10-20
-- updated on 2026-10-26
