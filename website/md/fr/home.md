# Qu'est-ce que lemma.cn
  <br>

[lemma.cn](../index.php) est une bibliothèque interactive de théorèmes formalisés pour les algorithmes. Le projet a d'abord été développé en [Python](../../py/website/index.php), avec le système de calcul symbolique open source [SymPy](https://github.com/sympy/sympy) pour l'exploration interactive ; la nomenclature des fonctions s'inspire surtout des conventions de [Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). Pour une rigueur logique et une vérifiabilité accrues, le cœur de la bibliothèque a été migré vers l'assistant de preuve [Lean 4](https://github.com/math-proof/lemma/tree/main), fondé sur la théorie des types dépendants (DTT).

Ses traits principaux se résument ainsi : **preuve interactive (ITP)**, **axiomatisation** et **programme comme preuve (Curry–Howard)**. Les objectifs de conception incluent une syntaxe précise, une expression concise, une exécution effective et une présentation claire, en mettant en valeur la symétrie des structures mathématiques et l'unité de la théorie.

* **Interactive** : on ne peut pas encore s'appuyer sur la preuve automatique des théorèmes (ATP) pour tout ; le démonstrateur consulte la bibliothèque et guide le système dans le choix des étapes et des lemmes existants.
* **Axiomatisation** : dans le cadre de la théorie des types dépendants, chaque résultat établi se déduit en un nombre fini d'étapes à partir de schémas d'axiomes et de règles d'inférence ; cette orientation, inspirée du [programme formaliste de Hilbert](https://en.wikipedia.org/wiki/Hilbert%27s_program), privilégie la reproductibilité des preuves plutôt que les raccourcis du langage naturel.
* **Programme comme preuve** : par l'isomorphisme de Curry–Howard, les propositions sont codées exactement en [Lean](https://lean-lang.org/) ; la preuve est un programme bien typé, sans recourir à des formules du type « évidemment », « il est facile de voir », « de même », « en général », « et ainsi de suite », « réciproquement », « pour conclure », « sans perte de généralité » à la place d'un enchaînement vérifiable ; sous la sémantique exacte des réels et hyperréels de Lean 4, il n'y a pas d'erreur d'arrondi en virgule flottante comme dans le code numérique ordinaire.

Le site est accessible via Google : [定理库](https://www.google.com.hk/search?q=%E5%AE%9A%E7%90%86%E5%BA%93). Parmi les assistants de preuve et bibliothèques open source apparentés : [Lean/mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html), [Coq](https://github.com/coq/coq) et [Isabelle](https://isabelle.in.tum.de/).

Pour maîtriser ce système de dérivation, il est utile de connaître les modes de raisonnement suivants et leurs tactiques Lean associées :

## Stratégies de raisonnement formalisé

1. **Induction**  
   Induction mathématique : établir une propriété sur les entiers naturels (ou une structure bien fondée) par le cas de base et l'hérédité. Tactique : `induction`
2. **Déduction**  
   Passage du général au particulier, avec introduction et élimination de quantificateurs universels. Tactiques : `specialize` / `intro` / `rintro`
3. **Preuve par l'absurde**  
   Raisonnement par l'absurde : supposer la négation de la conclusion et dériver une contradiction via le [tiers exclu](../?module=Bool.Or_Not). Tactique : `by_contra`
4. **Diviser pour régner**  
   Analyse par cas : décomposer l'objectif en cas mutuellement exclusifs et exhaustifs. Tactiques : `by_cases` / `interval_cases` / `rcases`
5. **Raisonnement abductif**  
   Recherche à rebours : partir du but et identifier des conditions suffisantes ou des lemmes applicables. Tactiques : `refine` / `apply`

## Raisonnement heuristique

- **Analogie**  
  Transporter un résultat connu d'une structure mathématique à une autre (par exemple des réels aux hyperréels) pour tester si la proposition subsiste.

<br><br>
------


# Construction de la bibliothèque algorithmique
  <br>

La bibliothèque contient environ <label id=count>5000</label> théorèmes établis (environ <label id=lines>100000</label> lignes de code Lean), disponibles pour la dérivation interactive et la consultation. Domaines principaux :

* [Bool](../?module=Bool) Logique propositionnelle et opérations booléennes
* [Fin](../?module=Fin) Algèbre élémentaire sur des indices finis
* [Nat](../?module=Nat) Algèbre élémentaire des entiers naturels
* [Int](../?module=Int) Algèbre élémentaire des entiers relatifs
* [Rat](../?module=Rat) Algèbre élémentaire des rationnels
* [Real](../?module=Real) Algèbre et analyse réelle
* [Hyperreal](../?module=Real) Analyse non standard
* [Complex](../?module=Complex) Analyse complexe, p. ex. :
  - [équation quartique](../?module=Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddMul_Pow_4.Ne_0)
* [Set](../?module=Set) Théorie des ensembles
* [Finset](../?module=Set) Ensembles finis
* [List](../?module=List) Théorie des listes
* [Vector](../?module=Vector) Vecteurs (tenseurs unidimensionnels)
* [Tensor](../?module=Tensor) Calcul tensoriel formalisé, sémantiquement aligné sur **torch.Tensor**, pour la spécification et la vérification formelle d'algorithmes d'apprentissage profond, p. ex. :
  - [kv_cache](../?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T)

<br><br>
-------

Cette bibliothèque s'adresse à la recherche en algorithmique et en formalisation mathématique — une métaphore de **dynamo pour la pensée**: formuler les propriétés algorithmiques comme propositions vérifiables par machine et les prouver pas à pas ; organiser et retrouver les lemmes pour raccourcir les arguments manuels répétitifs ; maintenir les scripts de preuve dans l'éditeur en ligne, avec commentaires, source Lean 4 et formules LaTeX présentés de façon structurée.

Elle s'adresse aux étudiants et chercheurs en mathématiques et domaines voisins, aux concepteurs et analystes d'algorithmes, ainsi qu'aux lecteurs qui consultent des preuves formalisées pour l'enseignement ou l'autoformation. La bibliothèque constitue une référence algorithmique électronique, interactive et consultable, rédigée en Lean 4.

<br><br>

![](png/national_emblem.png)
[<font size=2>浙公网安备33060202000937号</font>](http://www.beian.gov.cn/portal/registerSystemInfo?recordcode=33060202000937)
[<font size=2>浙ICP备20017509号-3</font>](https://beian.miit.gov.cn/)

<script type=module>
	$('#count').innerHTML = await get("../php/request/count.php");
  $('#lines').innerHTML = await get("../php/request/lines.php");
</script>
