# lemma

reference website:

https://www.lemma.cn/lean/website/index.php

the latex is printed with the aid of the following project:

https://github.com/KaTeX/KaTeX
## quick start
```bash
git clone https://github.com/cosmosZhou/lemma.git
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
versionNumber=4.23.0
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
LogExpSum  
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
| infix operators  | prefix operators |
| :--: |  :--: | 
| X.eq.Y | EqXY | 
| X.ne.Y | NeXY | 
| X.gt.Y | GtXY | 
| X.lt.Y | LtXY | 
| X.ge.Y | GeXY | 
| X.le.Y | LeXY | 
| X.in.Y | InXY | 
| X.is.Y | IffXY | 
| X.as.Y | SEqXY | 
| X.or.Y | OrXY | 
| X.and.Y | AndXY | 
| X.dvd.Y | DvdXY | 
| X.sub.Y | SubsetXY | 
| X.sup.Y | SupsetXY | 
