# Purpose of this project
This is Lean 4 machine learning project (related to Torch, SymPy, [KaTeX](https://github.com/KaTeX/KaTeX), and [arXiv](https://arxiv.org)):
👉 **[https://github.com/math-proof/lemma](https://github.com/math-proof/lemma)**

The main goals of this project are formalizing in Lean4:

* **machine learning framework Torch**
  The most commonly used Torch operators — such as `softmax`, `sum`, `mean`, `unsqueeze`, `matmul`, `repeat`, `permute`, `transpose`, `exp`, and `log` — have already been translated into Lean 4.

* **symbolic mathematics from SymPy (symbolic mathematics for Python).**
  SymPy is also a fundamental algorithmic component of the PyTorch framework.

* **mathematical foundations of reinforcement learning**
  This part is based on the reference book [*Mathematical Foundation of Reinforcement Learning*](https://github.com/MathFoundationRL/Book-Mathematical-Foundation-of-Reinforcement-Learning) and is still in progress.

* **mathematical arguments from arXiv machine learning papers.**
  For example:
  [Tensor.DivSumSSum.eq.MeanDivSum_MeanSum](http://www.lemma.cn/lean/index.php?module=Tensor.DivSumSSum.eq.MeanDivSum_MeanSum)
  This theorem formalizes and proves a claim from a reinforcement learning paper on arXiv.
  More examples can be found in the theorem library at [www.lemma.cn](http://www.lemma.cn).


It also ficilitates reading by visualizing Lean 4 code with KaTeX. 
This feature converts one-dimensional Lean code into rainbow-colored KaTeX-rendered mathematical formulas. Over **240,000 theorems from Mathlib** have already been visualized in KaTeX format, for example:
  [http://www.lemma.cn/lean/?mathlib=Finset.*sum](http://www.lemma.cn/lean/?mathlib=Finset.*sum)
  (You can use any regular expression to search.)

## quick start
```bash
git clone https://github.com/math-proof/lemma.git
cd lemma
# suppose you have installed lean already
lake clean
lake build
# for Windows
# . ps1/run.ps1
# for Linux
bash sh/run.sh
```

# install
## lean
### build from binary
check https://github.com/leanprover/lean4/tags to see the available installer for your system.  
for linux: (better to use VPN to download, using a browser not by wget!)
```sh
# suppose ~/github is your working directory and the binary installer file is copied here.
cd ~/github
versionNumber=4.24.0
# prepare zstd
# Ubuntu/Debian
sudo apt install zstd
# CentOS/RHEL
sudo yum install zstd

tar -I zstd -xf lean-$versionNumber-linux.tar.zst
# tar --use-compress-program=zstd -xvf lean-$versionNumber-linux.tar.zst
echo 'export PATH="$PATH:~/github/lean-$versionNumber-linux/bin"' >> ~/.bashrc
source ~/.bashrc
```

### build from source
```bash
# install prerequisites
yum install gmp-devel 
yum install libuv libuv-devel
git clone https://github.com/leanprover/lean4
cd lean4
cmake --preset release
make -C build/release -j$(nproc || sysctl -n hw.logicalcpu)
```

## elan
check https://github.com/leanprover/elan/tags to see available installer for your system.  
for linux:  
```bash
# suppose ~/github is your working directory
cd ~/github
wget https://github.com/leanprover/elan/releases/download/v4.1.2/elan-x86_64-unknown-linux-gnu.tar.gz
tar -xzf elan-x86_64-unknown-linux-gnu.tar.gz
# ./elan-init -y --default-toolchain stable
# skipping the stable default-toolchain installation
./elan-init -y
# check environment settings, or restart your terminal
cat ~/.bashrc
cat ~/.bash_profile
cat ~/.profile
elan toolchain link v$versionNumber ~/github/lean-$versionNumber-linux
elan default v$versionNumber
elan show

lake --version
lean --version
elan --version
# update elan using command
elan self update
```

### install lean using elan
in linux, this is not suggested due to slow network.
```sh
elan toolchain install stable
elan default stable
```
in windows (https://github.com/PowerShell/PowerShell/releases/download/v7.5.3/PowerShell-7.5.3-win-x64.msi)
```ps1
elan default leanprover/lean4:v$versionNumber
# install a particular version
elan toolchain install leanprover/lean4:$versionNumber
```
## Update mathlib4 using commit-id
use the following script to automatically and incrementally update the dependency git projects required by mathlib4
```sh
bash sh/update.sh
```
```ps1
. ps1/update.ps1
```

## Start lake server manually
```sh
lake serve -- yourProjectDir
```

# trouble-shooting for VSCode

## Error loading webview

Error: Could not register service worker: InvalidStateError: Failed to register a ServiceWorker: The document is in an invalid state..

### solution
Clear VSCode's Cache: If some cached data is causing the error, clearing the cache might help.

Remove cache directories:
- [ ] On Windows: C:\Users\<YourUsername>\AppData\Roaming\Code
- [ ] On Mac: ~/Library/Application Support/Code
- [ ] On Linux: ~/.config/Code

Be cautious with this step as it will reset some settings and extensions might need re-installation.

## Network Issue when installing from github
solutions:
- [ ] install Lean4 extension in VSCode
- [ ] find a linux machine that can use lean4 with no problem, and then scp -r ~/.elan yourName@TargetIPAddress:
- [ ] echo 'export PATH="$HOME/.elan/bin:$PATH"' >> ~/.profile on the Target machine
- [ ] scp -r yourLeanProject yourName@TargetIPAddress:targetFolder/
Now you can work on yourLeanProject on your Target machine with no trouble.

# related projects
https://github.com/ImperialCollegeLondon/FLT

# paper to read
```
https://lean-lang.org/doc/reference/latest/
https://zhuanlan.zhihu.com/p/695704489
https://github.com/Goedel-LM/Goedel-Prover
https://github.com/deepseek-ai/DeepSeek-Prover-V1.5
https://arxiv.org/abs/2408.08152v1
https://arxiv.org/abs/2502.03438
https://aclanthology.org/2024.emnlp-main.667
https://github.com/leanprover-community/repl
https://leanprover-community.github.io/mathlib4_docs/index.html
https://arxiv.org/abs/2504.06122
https://mml-book.github.io/book/mml-book.pdf
https://mml-book.github.io/
https://help.aliyun.com/zh/model-studio/what-is-model-studio
https://arxiv.org/abs/2504.11354
https://teorth.github.io/analysis/
https://arxiv.org/abs/2505.23754
https://www.arxiv.org/abs/2507.15855
https://github.com/MathFoundationRL/Book-Mathematical-Foundation-of-Reinforcement-Learning
https://arxiv.org/abs/2310.05328
```
cd repl
lake update -R && lake build
lake exe repl

# lean-web
https://live.lean-lang.org/
https://github.com/leanprover-community/lean4web/blob/main/doc/Usage.md
https://www.leanprover.cn/projects/lean4web/
https://github.com/hhu-adam/lean4web-tools
https://github.com/leanprover-community/lean4web

# Lemma Naming Convention
## CamelCase
CamelCase is used for unary function, eg:  
LogSumExp denotes the expression: (exp x).sum.log
generally, if F is a unary function, and X is its argument, then
FX denote the expression: F X

## Snake_Case
Snake_Case is used for binary function, eg:  
Eq_Log  
generally, if F is a binary function, and Y is its second argument, then
F_Y denote the expression: F _ Y
wherein:
- _ (wild card) denotes any types of X
- Y is the given type for the second argument of F

## Apostrophe
Apostrophe is used to separate consecutive digits, eg: 
Div1'2 denotes: 1 / 2
Apostrophe is introduced to resolve ambiguity, otherwise 1 / 2 will have to be written as:  
DivOneTwo, etc.

## Infix Operators
small-letter binary infix operators are short name for Capital-letter operator name, eg:
| infix operators  | prefix operators | sympy equivalent |
| :--: |  :--: |  :--: | 
| X.eq.Y | EqXY | Equal | 
| X.ne.Y | NeXY | Unequal | 
| X.gt.Y | GtXY | Greater |
| X.lt.Y | LtXY | Less |
| X.ge.Y | GeXY | GreaterThan |
| X.le.Y | LeXY | LessThan
| X.in.Y | InXY | Contains | 
| X.is.Y | IffXY | Equivalent | 
| X.as.Y | SEqXY | -- | 
| X.ou.Y | OrXY | Or | 
| X.et.Y | AndXY | And | 
| X.dvd.Y | DvdXY | -- | 
| X.sub.Y | SubsetXY | Subset | 
| X.sup.Y | SupsetXY | Supset | 

## Plural S
The English Plural Letter S is used to denote double occurrence of types:
- EqSumS is short for : Sum.eq.Sum
- SEqSumSGet is short for : SumGet.as.SumGet
