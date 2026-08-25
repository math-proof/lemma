# Raisonnement symbolique et preuve automatique : historique du projet

<br>

## 2008 — Preuve axiomatique fondée sur le calcul symbolique

À partir de 2008, en apprenant le C++, l’auteur entreprend un travail de long terme : construire un environnement de preuve **axiomatique et vérifiable par machine**, pour assister le raisonnement complexe et explorer une automatisation progressive. Le projet avance surtout sur le temps libre. La première implémentation est en C++, appuyée sur la bibliothèque open source allemande [GiNaC](https://www.ginac.de/), avec une dérivation semi-mécanisée par calcul symbolique.

Faute de compétences plus larges à l’époque, le C/C++ est le langage principal. Son empreinte persiste dans le style de code, par exemple :

- Sortie d’équations façon opérateur surchargé : `Eq << Equal(a, b)` (analogue à `cout << "Hello World";`)
- Notation lambda en LaTeX : `Lamda[k] (h[k])`, proche des lambdas C++ `[k]{return h[k];}`
- Opérations sur les objets via `this`, p. ex. `Eq << Eq[-1].this.rhs.simplify()`

## 2016 — Écosystème open source et « programme comme preuve »

Vers 2016, l’auteur découvre plusieurs ressources de calcul symbolique et d’assistance à la preuve : [SymPy](https://www.sympy.org/en/index.html) et son sous-projet C++ [SymEngine](https://github.com/symengine/symengine), [Maxima](http://maxima.sourceforge.net) (Common Lisp), l’environnement intégré [SageMath](https://www.sagemath.org/) (Maxima, [Maple](https://www.maplesoft.com/products/Maple/), Mathematica, [MATLAB](https://www.mathworks.com/products/matlab.html), SymPy, etc.), le [Theorem Prover Museum](https://theoremprover-museum.github.io/), ainsi que la littérature sur les [assistants de preuve](https://en.wikipedia.org/wiki/Proof_assistant) et les [systèmes de preuve interactive](https://en.wikipedia.org/wiki/Interactive_proof_system).

Plusieurs années de lecture et d’expérience ancrent la [correspondance de Curry–Howard](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence) (« preuve comme programme ») comme base architecturale. Python devient dominant en algorithmique et en apprentissage automatique : développement plus rapide qu’en C++ (exécution souvent plus lente), syntaxe proche des mathématiques. Le projet est progressivement **réécrit en Python**.

## 2018 — lemma.cn et bibliothèque ouverte

En 2018, l’auteur crée le site [lemma.cn](../axiom) pour publier l’outil semi-mécanisé et la bibliothèque de théorèmes. L’objectif est une collaboration open source pour étendre la couverture formelle ; à grande échelle, la bibliothèque pourrait alimenter des méthodes d’apprentissage, mais un corpus entièrement formalisé reste un effort collectif de long terme.

## 2021 — Raisonnement symbolique et modèles neuronaux (Inter-GPS)

En 2021, Lupantech et al. publient **Inter-GPS**, solveur géométrique basé sur Transformer, combinant énoncés formels, données à grande échelle, modèles séquentiels et étapes symboliques — une voie de référence vers la résolution automatique : langage formel, corpus d’entraînement, prédiction de séquences d’invocation de théorèmes, achèvement par algorithmes symboliques.

- Page du projet : <https://lupantech.github.io/inter-gps/>
- Code : <https://github.com/lupantech/InterGPS>
- Article : <https://arxiv.org/pdf/2105.04165.pdf>

## 2023 — Supervision de processus et données formelles (OpenAI)

En 2023, OpenAI publie environ **800 000** exemples liés à la supervision de processus pour le raisonnement mathématique :

- <https://openai.com/research/improving-mathematical-reasoning-with-process-supervision>
- Article : <https://arxiv.org/abs/2305.20050>

L’auteur esquisse aussi une « math GPT » formelle : (1) **couche logique formelle** en Python (puis Lean, etc.), le langage naturel réservé à l’exposition ; (2) **modèle de récompense** guidé par l’interpréteur (p. ex. LaTeX) ; (3) **apprentissage par renforcement** sur du code généré. Cela rejoint la voie actuelle **agents de codage LLM + vérification par noyau** ; la confiance repose sur la vérification formelle, non sur le texte du modèle.

## 2024 — Noyau Lean 4 et dépôt à double branche

À partir de 2024, la bibliothèque centrale migre vers [Lean 4](https://lean-lang.org/) en théorie des types dépendants ([math-proof/lemma](https://github.com/math-proof/lemma), branche `main`). L’exploration interactive [SymPy](https://www.sympy.org/en/index.html) avec `apply`/`prove` reste sur `master` — double piste **preuves vérifiées par noyau** et **interaction symbolique**. Environ **5000** théorèmes et **100 000** lignes Lean couvrent le calcul `Tensor`, l’analyse réelle et des propriétés algorithmiques. [lemma.cn](../index.php) propose recherche (`index.php?q=…`), vues callee/caller et présentation Lean/LaTeX en ligne.

## 2025 — Feuille de route, agents et formalisation d’algorithmes

Vers 2025, le projet publie une [feuille de route](../endeavour) : phase 2, **un million** de théorèmes ( [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) étant déjà à l’échelle **100 000** en Lean) ; phase 3, **agents de codage LLM** en boucle homme–machine, alignés sur des outils ancrés au dépôt (Cursor Agent, LeanDojo, etc.). Côté algorithmes, l’identité d’attention incrémentale du **KV cache** pour le décodage GPT a été formalisée en SymPy et Lean 4 (voir [note KV cache](../arxiv/kv_cache/main.md) ; PDF arXiv en attente), illustrant le passage de sémantiques d’algorithmes de production à des lemmes vérifiables.
