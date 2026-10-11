import Mathlib
import sympy.Basic
import Lemma.AdicCompletion.IsCompact.LocalLevelOne
import Lemma.Ideal.Support.AdelicDockFinEmbed
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdicCompletion Ideal


/--
[AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdelicDock_finEmbed_localEmbed_mem_levelOne_inf_finiteAdelicGL2Subgroup.lean)
-/
private lemma isLocalLevelOne_of_integral
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
  {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
  (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) :
  AdelicDock.IsLocalLevelOne (𝓞 F) F v N m := by
  have hN : N ≠ ⊥ := fun h => hv (h ▸ dvd_zero _)
  have hb : AdelicLevel.idealBound (𝓞 F) N v = 1 :=
    AdelicLevel.idealBound_eq_one_of_not_dvd hN hv
  refine ⟨hm, ?_, ?_⟩
  ·
    rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  ·
    rw [hb]
    exact (mem_adicCompletionIntegers _ _ _).mp (sub_mem (hm 1 1) (one_mem _))

private lemma entries_mem_of_mem_integralSubgroup
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {k : GL (Fin 2) (v.adicCompletion F)}
  (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) (i j : Fin 2) :
  (k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F := by
  obtain ⟨y, rfl⟩ := hk
  rw [Matrix.GeneralLinearGroup.map_apply]
  exact SetLike.coe_mem _

private lemma mem_localLevelOne_of_mem_integralSubgroup
  (F : Type*)
  [Field F]
  [NumberField F]
  (v : HeightOneSpectrum (𝓞 F))
  {N : Ideal (𝓞 F)} (hv : ¬ v.asIdeal ∣ N)
  {k : GL (Fin 2) (v.adicCompletion F)}
  (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
  k ∈ AdelicDock.localLevelOne (𝓞 F) F v N := by
  rw [AdelicDock.mem_localLevelOne_iff]
  exact ⟨isLocalLevelOne_of_integral F v hv (entries_mem_of_mem_integralSubgroup F v hk),
    isLocalLevelOne_of_integral F v hv
      (entries_mem_of_mem_integralSubgroup F v (inv_mem hk))⟩

@[path]
private lemma main
  [Field F] [NumberField F]
  {v : HeightOneSpectrum (𝓞 F)}
  {N : Ideal (𝓞 F)}
  {k : GL (Fin 2) (v.adicCompletion F)}
-- given
  (hv : ¬ v.asIdeal ∣ N)
  (hk : k ∈ integralSubgroup (v.adicCompletionIntegers F) (v.adicCompletion F)) :
-- imply
  finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v k) ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
-- proof
  refine mem_inf_of_components F (glArch_finEmbed (𝓞 F) F _) fun w => ?_
  if hw : w = v then
    subst hw
    rw [glFin_finEmbed, finComponent_localEmbed_self]
    exact mem_localLevelOne_of_mem_integralSubgroup F _ hv hk
  else
    rw [glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]
    exact one_mem _


-- created on 2026-10-10
