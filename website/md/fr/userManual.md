# Manuel utilisateur — bibliothèque formelle Lean 4

## Utilisation en ligne

### Recherche de théorèmes

Le site Lean 4 est servi par `index.php` à la racine du dépôt (URL locales typiques : [http://localhost:8080/lean/index.php](http://localhost:8080/lean/index.php) ou [http://localhost/lean/index.php](http://localhost/lean/index.php), selon la racine PHP et le port). Sans paramètre de requête, un résumé de la bibliothèque s’affiche ; utilisez la zone de recherche (en haut à droite) ou une URL GET.

**Recherche de base** : correspondance de sous-chaîne sur les noms de modules en base (au plus `limit` résultats, 100 par défaut). Exemples :

- [../../../index.php?q=Icc&limit=100](../../../index.php?q=Icc&limit=100) — modules dont le nom contient `Icc`
- [../../../index.php?q=kv_cache&limit=50](../../../index.php?q=kv_cache&limit=50) — modules dont le nom contient `kv_cache`
- [../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T](../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) — ouvrir directement le lemme principal KV-cache

Le placeholder de recherche est `input a hint in search of a formula/theorem/axiom`. Options (cases à cocher ou paramètres d’URL) :

- `limit` — nombre maximal de résultats (défaut 100)
- `caseSensitive=on` — respect de la casse
- `wholeWord=on` — mot entier
- `regularExpression=on` — expression régulière (p. ex. `q=Tensor\..*BandPart&regularExpression=on`)
- `fullText=on` — recherche dans les sources `Lemma/**/*.lean` (p. ex. `q=band_part&fullText=on`)
- `latex=on` — similarité de formules LaTeX (service backend requis)

Raccourcis (focus dans la recherche) : Alt+C / W / R / L / U basculent Case / WholeWord / Regex / LaTeX / FullText ; Ctrl+F focus la recherche.

![zone de recherche](png/search/panel.png)

Saisissez un mot-clé (p. ex. `Icc`, `DotSoftmax`, `kv_cache`) et validez ; cliquez un résultat pour ouvrir la page du lemme.

![mot-clé de recherche](png/search/keyword.png)

La page de résultats affiche `search results` et le nombre de correspondances. Cliquez un nom de module pour voir given / imply / proof.

![résultats de recherche](png/search/results.png)

### Dépendances entre lemmes (callee / caller)

Chaque page de lemme comporte **-- given**, **-- imply** et **-- proof**. Les dépendances viennent du champ `imports` : si le lemme A a `Lemma.B` dans `imports`, alors A utilise B dans sa preuve.

Terminologie (libellés anglais et paramètres d’URL sur le site) :

- **callee hierarchy** (lien sur `-- imply`, `?callee=module`) : lemmes qui *importent ce module* — autres résultats dont `imports` contient le module courant (qui dépend de ce résultat).
- **caller hierarchy** (lien sur `-- proof`, `?caller=module`) : lemmes *importés par ce module* — entrées de la liste `imports` du module courant (ce que cette preuve appelle).

Sur la page de hiérarchie, basculez entre vues callee et caller ; ajoutez `#deep` pour déplier l’arbre complet ; `>>>>` / `<<<<` déplient ou replient un niveau.

#### Hiérarchie callee (qui utilise ce lemme)

Exemple : le [lemme principal KV-cache](../../../index.php?module=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T).

Sur la page du lemme, survolez le lien à gauche de **-- imply** ; l’infobulle indique `callee hierarchy` :

![lien callee](png/hierarchy/hyperlink.png)

Cliquez pour ouvrir le graphe callee, p. ex. [`?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`](../../../index.php?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) :

![hiérarchie callee](png/hierarchy/callee.png)

Le graphe liste les lemmes dont `imports` référence ce module (le cas échéant).

- `>>>>` développe les dépendants ; `<<<<` replie.
- [`?callee=…#deep`](../../../index.php?callee=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T#deep) déplie tout l’arbre callee.

#### Hiérarchie caller (ce que ce lemme utilise)

Sur la page du lemme, cliquez le lien `caller hierarchy` à gauche de **-- proof**, p. ex. [`?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T`](../../../index.php?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T) :

![hiérarchie caller](png/hierarchy/caller.png)

Le graphe liste les lemmes importés par cette preuve (p. ex. `Tensor.DotSoftmaxAdd_Mul_Infty.eq.Stack_DotSoftmaxDivDot_T` (lemme `gpt`), `Tensor.Stack.eq.AppendStackS`, etc.).

- [`?caller=…#deep`](../../../index.php?caller=Tensor.GetSlice.eq.Append_DotSoftmaxDivDot_Append.of.All_Eq_DotSoftmaxAdd_DivDot_T#deep) déplie tout l’arbre caller.

![hiérarchie caller profonde](png/hierarchy/deep/caller.png)

## Déploiement local

Prérequis : serveur web PHP, MySQL (index des théorèmes), toolchain Lean 4, et le dépôt [math-proof/lemma](https://github.com/math-proof/lemma). Configurez `DocumentRoot` PHP sur la racine du clone (contenant `index.php` et `Lemma/`).

Exemple Linux (détails PHP : [php installation.docx](../php%20installation.docx)) :

```bash
cd /usr/local
git clone https://github.com/cosmosZhou/shell.git
cd shell/php
make
sh start.sh port=80 DocumentRoot=/home/github/lean
```

Exemple Windows :

1. Racine web, p. ex. `E:\github\lean`, et `DOCUMENT_ROOT` selon php installation.docx.
2. Cloner : `git clone --depth=1 https://github.com/math-proof/lemma.git`
3. Installer Lean 4 (`lean-toolchain`), exécuter `lake build`, mettre à jour l’index MySQL (p. ex. `ps1/update.ps1`).
4. Dans le navigateur (adapter le port) :
   - [http://localhost/lean/index.php](http://localhost/lean/index.php)
   - ou [http://localhost:8080/lean/index.php?q=Icc&limit=100](http://localhost:8080/lean/index.php?q=Icc&limit=100)
