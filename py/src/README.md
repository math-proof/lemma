# GCC Installation Manual
## Compiler installation

### mingw64 for Windows

使用mingw64编译器。
下载地址为：
https://sourceforge.net/projects/mingw-w64/files/Toolchains%20targetting%20Win64/Personal%20Builds/mingw-builds/
选择x86_64不要选择i686！

解压即完成安装，设置环境变量：
MINGW_HOME = D:\Program Files\mingw64
‘D:\Program Files\mingw64’是你安装mingw64的安装路径；
把 
%MINGW_HOME%\bin
加入PATH，重新启动PC,即可生效。


### the difference between MinGW SEH and MinGW SJLJ:
- SJLJ and SEH are two different exception handling systems.
- For the specific differences, the resources you've already seen cover everything.
- However, as for which one is better to install, go with SJLJ unless you know that you need SEH.
- SJLJ is more widely supported across architectures, and is more robust. Also, SJLJ exceptions can be thrown through libraries that use other exception handling systems, including C libraries. However, it has a performance penalty.
- SEH is much more efficient (no performance penalty), but unfortunately is not well-supported. SEH exceptions will cause bad things to happen when thrown through libraries that do not also use SEH. As far as your code is concerned, there are no real differences. You can always switch compilers later if you need to.


### 安装、调试和开发的参考网址
https://www.jianshu.com/p/c3411fe5b19c
https://www.cnblogs.com/fanyizhan/p/10314762.html
https://www.cnblogs.com/ggg-327931457/p/9694516.html
https://blog.csdn.net/yangyangyang20092010/article/details/46350519
https://sourceforge.net/projects/mingw-w64/
https://sourceforge.net/projects/mingwbuilds/files/external-binary-packages/
http://www.gnu.org/software/gdb/download/
https://blog.csdn.net/ksws0292756/article/details/78505240


### make
- 安装make, 找到D:\Program Files\mingw64\bin\mingw32-make.exe
复制后将其重命名为D:\Program Files\mingw64\bin\make.exe即可！
- cmd下输入make -v
得到以下结果：
GNU Make 4.2.1
Built for x86_64-w64-mingw32
Copyright (C) 1988-2016 Free Software Foundation, Inc.
License GPLv3+: GNU GPL version 3 or later <http://gnu.org/licenses/gpl.html>
This is free software: you are free to change and redistribute it.
There is NO WARRANTY, to the extent permitted by law.

### 获取gcc预定义宏
gcc -posix -E -dM -<nul

### jni
对于jni项目，作以下设置：
将以下目录添加到-I选项中：
"${JAVA_HOME}/include"
"${JAVA_HOME}/include/win32"
注意一定要有双引号！，而且JAVA_HOME已经设置成系统环境变量！
JAVA_HOME = C:\Program Files\Java\jdk1.8.0_111
然后在cpp文件就可以引用jni头文件了！
#include <jni.h>

### Eigen matrix library
http://eigen.tuxfamily.org/index.php?title=Main_Page

## VSCode debugging
### extension to install
- C/C++
- C/C++ Themes
- C/C++ Extension Pack

### select C/C++ debug mode

this is specified at the [launch.json](.vscode/launch.json) file, together with the build stage which is set at the [tasks.json](.vscode/tasks.json). 

the task label is selected automatically by settings of launch.json

### set breakpoint and debug
debug [main.cpp](src/main.cpp) is simple: set breakpoint at any line of the source file and press F5

