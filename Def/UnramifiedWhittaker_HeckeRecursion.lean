import Lemma.AdelicDock.LocalEmbedding

set_option autoImplicit false

noncomputable section

open Matrix

namespace UnramifiedWhittaker

def heckeRecursionSeq (N lam om : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam / N
  | m + 2 => (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N

def torusFactor (N lam om : ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m then heckeRecursionSeq N lam om m.toNat else 0

section Matrices

variable {K : Type*} [Field K]

def unipotent (x : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [det_fin_two_of])

def diagZ (π : K) (hπ : π ≠ 0) (m : ℤ) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π ^ m, 0; 0, 1] (by simp [det_fin_two_of, zpow_ne_zero m hπ])

def repSome (π : K) (hπ : π ≠ 0) (β : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, β; 0, 1] (by simp [det_fin_two_of, hπ])

def repInf (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π] (by simp [det_fin_two_of, hπ])

def scalarPi (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, 0; 0, π] (by simp [det_fin_two_of, hπ])

end Matrices

section Adelic

open IsDedekindDomain NumberField AdelicDock

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def placeEmbed (v : HeightOneSpectrum R) :
    GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (AdeleRing R K) :=
  (finEmbed R K).comp (localEmbed R K v)

end Adelic

end UnramifiedWhittaker

end
