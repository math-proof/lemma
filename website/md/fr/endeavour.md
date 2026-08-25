# Feuille de route de recherche

[lemma.cn](../../index.php) vise à long terme la **mécanisation des mathématiques**, dans une direction proche du [Key Laboratory of Mathematics Mechanization, CAS](http://www.mmrc.iss.ac.cn/). La preuve mathématique entièrement automatique reste un problème ouvert pour les ressources formelles accessibles au public. Ce projet vise à construire progressivement une bibliothèque de théorèmes et un environnement de preuve **axiomatiques, vérifiables par machine et open source**.

La bibliothèque contient environ 5000 théorèmes vérifiés en Lean 4 (voir le compteur sur la page d’accueil), couvrant plusieurs domaines. Phases envisagées :

1. **Preuve interactive fondée sur des règles (largement en place)**  
   Un environnement semi-mécanisé basé sur la théorie des types dépendants et une bibliothèque de lemmes est opérationnel ; travail en cours : corrections, extension des lemmes et outillage.

2. **Corpus de théorèmes à grande échelle (en cours)**  
   Objectif : **un million** de théorèmes formels réutilisables dans le cadre unifié de ce projet (calcul `Tensor` et domaines associés). [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) dans l’écosystème Lean a déjà atteint l’échelle des **100 000**, ce qui montre la faisabilité en théorie des types dépendants ; ce projet vise une couverture formelle de l’ordre de grandeur de l’ensemble des théorèmes mathématiques démontrés par l’humanité (environ **un million**). Effort de long terme, communautaire ; l’échéance dépend du volume de contributions.

3. **Agents de codage LLM pour l’aide à la preuve (en cours)**  
   Sur la bibliothèque de la phase 2 et les sources Lean, appliquer le paradigme actuel des **coding agents** : les grands modèles de langage travaillent en boucle **homme–machine** — lecture du contexte du dépôt, appels d’outils (recherche de lemmes, `lake build`, diagnostics LSP, graphes callee/caller, etc.), rédaction ou complétion de scripts de preuve ; l’humain relit et corrige, le **noyau Lean 4** reste l’autorité finale. Même schéma que les agents les plus avancés en génie logiciel — **ancrage au dépôt** (RAG / indexation du code), **usage d’outils** (terminal, build, serveur de langage), boucle **édition–compilation–correction** (p. ex. [Cursor Agent](https://cursor.com/), GitHub Copilot, Claude Code) — pour accélérer la recherche de lemmes, le choix de tactiques et l’esquisse de preuves, **sans remplacer** la vérification formelle. Travaux connexes : [LeanDojo](https://leandojo.org/) (preuve de théorèmes Lean avec RAG), [ProofNet](https://proofnet.github.io/) (benchmark d’autoformalisation Lean de mathématiques de licence), [GPT-f](https://arxiv.org/abs/2109.04561) (première génération de preuve formelle assistée par LLM) ; ce projet privilégie l’intégration des coding agents à la bibliothèque **lemma.cn** et à son interface de recherche, plutôt que des compétitions de preuve entièrement automatiques.

4. **Découverte de théorèmes semi-supervisée / non supervisée (recherche)**  
   Explorer la proposition de énoncés candidats à partir de la bibliothèque existante et des tentatives de preuve à partir des lemmes connus, en distinguant strictement conjectures et théorèmes vérifiés.

5. **Unification langages mathématiques abstraits et langages de programmation (long terme)**  
   S’appuyer sur les étapes précédentes pour que les systèmes informatiques expriment, composent et vérifient plus systématiquement les structures mathématiques abstraites, comme infrastructure pour la recherche et la vérification formelle d’algorithmes.

Cette feuille de route décrit des orientations et jalons de recherche, sans calendrier ni engagement technique garanti. Chaque phase peut avancer en parallèle de l’usage de la bibliothèque et des artefacts Lean 4 déjà publics.
