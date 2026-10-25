import Mathlib
import Def.LanglandsTunnell_OctahedralDatum
import Def.LanglandsTunnell_IsGaloisAttachmentOf
import Def.GaloisRep_ModThreeCyclotomic

set_option autoImplicit false

open AutomorphicForm WeierstrassCurve
open FLT.TunnellOctahedralGlobalCarrier FLT.Qepw139bOctahedralDatumLinkedRecarve
open scoped MatrixGroups

noncomputable section

namespace LanglandsTunnell

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

def TunnellExistsForAttachedOctahedralData (notionT : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ ρ : Γℚ →* GL (Fin 2) (ZMod 3), Continuous ρ → Function.Surjective ρ →
    (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) →
    ∀ (D : OctahedralGaloisDatumLinked ℚ (ℤ√(-2))) (S : Finset ℕ),
      IsGaloisAttachmentOf ρ D.toOctahedralGaloisDatum S →
      ∃ π : HeckeEigensystem ℚ (ℤ√(-2)),
        notionT.IsCusp ℚ π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached

def NotionInhabitedOverRat (notionD : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∃ π : HeckeEigensystem ℚ (ℤ√(-2)), notionD.IsCusp ℚ π

def NotionCompatForAttachedOctahedralData (notionT notionD : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ ρ : Γℚ →* GL (Fin 2) (ZMod 3), Continuous ρ → Function.Surjective ρ →
    (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) →
    ∀ (D : OctahedralGaloisDatumLinked ℚ (ℤ√(-2))) (S : Finset ℕ),
      IsGaloisAttachmentOf ρ D.toOctahedralGaloisDatum S →
      ∀ π : HeckeEigensystem ℚ (ℤ√(-2)),
        notionT.IsCusp ℚ π → HeckeEigensystem.AgreesAwayFromFinite π D.attached →
        notionD.IsCusp ℚ π

end LanglandsTunnell

end
