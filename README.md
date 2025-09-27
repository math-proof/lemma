# lemma

reference website:

https://www.lemma.cn/lean/website/index.php

the latex is printed with the aid of the following project:

https://github.com/mathjax/MathJax.git

# install
## lean
### build from binary
check https://github.com/leanprover/lean4/releases/tag/v4.18.0 to see the available installer for your system.  
for linux: (better to use VPN to download, using a browser not by wget!)
```sh
# suppose ~/gitlab is your working directory and the binary installer file is copied here.
cd ~/gitlab
# prepare zstd
# Ubuntu/Debian
sudo apt install zstd
# CentOS/RHEL
sudo yum install zstd

tar -I zstd -xf lean-4.18.0-linux.tar.zst
# tar --use-compress-program=zstd -xvf lean-4.18.0-linux.tar.zst
echo 'export PATH="$PATH:~/gitlab/lean-4.18.0-linux/bin"' >> ~/.bashrc
source ~/.bashrc

# yum install libgmp-dev
```

### build from source
install prerequisites
```sh
yum install gmp-devel 
yum install libuv libuv-devel
```

```sh
git clone https://github.com/leanprover/lean4
cd lean4
cmake --preset release
make -C build/release -j$(nproc || sysctl -n hw.logicalcpu)
```

## elan
check https://github.com/leanprover/elan/releases/tag/v4.0.0 to see available installer for your system.  
for linux:  
```sh
# suppose ~/gitlab is your working directory
cd ~/gitlab
wget https://github.com/leanprover/elan/releases/download/v4.0.0/elan-x86_64-unknown-linux-gnu.tar.gz
tar -xzf elan-x86_64-unknown-linux-gnu.tar.gz
# ./elan-init -y --default-toolchain stable
# skipping the stable default-toolchain installation
./elan-init -y
# check environment settings, or restart your terminal
cat ~/.bashrc
cat ~/.bash_profile
cat ~/.profile
elan toolchain link v4.18.0 ~/gitlab/lean-4.18.0-linux
elan default v4.18.0
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
in windows
```ps1
elan default leanprover/lean4:v4.18.0
# install a particular version
elan toolchain install leanprover/lean4:4.19.0
elan override set leanprover/lean4:4.19.0
```
## Update mathlib4 using commit-id
copy the content of https://github.com/leanprover-community/mathlib4/blob/aa936c36e8484abd300577139faf8e945850831a/lake-manifest.json and replace your own version with it. Then use the following script to automatically and incrementally update the dependency git projects required by mathlib4
```sh
bash sh/update.sh
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

# Naming Convention
## CamelCase
LogExpSum