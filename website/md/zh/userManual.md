<h1>半机械化数学定理库操作手册</h1>
<hr />
<h2>线上操作手册</h2>
<br>
<h3>定理检索功能</h3>
<p>
	启动软件网站可视化定理库<a href='../axiom/'>sympy/axiom</a>，或者定理库搜索界面<a
		href='../axiom/search'>sympy/axiom/search</a>如下图所示：
</p>
<img class=zoom src="png/search/panel.png" alt="搜索框" />
<hr />
<br>
<p>在箭头所指的提示符（input a hint for search of a
	theorem/axiom）搜索框中输入需要查找的数学定理的名称，或者定理名称的个别单词，比如binomial theorem
	中的binomial关键词，如下图所示：</p>
<img class=zoom src="png/search/keyword.png" alt="搜索关键词">
<hr />
<br>
<p>键入回车(Enter)之后，就可在前端打印出包含binomial单词的所有数学定理了：如下图所示：</p>
<img class=zoom src="png/search/results.png" alt="搜索关键词" />
<hr />
<br>
<p>
	按照箭头方向所指单击即可进入<a
		href='../axiom.php?module=Discrete.combinatorics.binomial.theorem'>牛顿二项式定理</a>的论证过程，
	用户也可以直接访问get api: <a href='../axiom.php?keyword=binomial'>www.axiom.top/sympy/axiom.php?keyword=binomial</a>
	来获取搜索结果。 图形界面和get api同时也支持<a
		href='http://www.regular-expressions.info/tutorial.html'>正则表达式</a>以及全字(whole
	word)匹配，比如： <a
		href='../axiom.php?keyword=Discrete.*binomial&regularExpression=true'>www.axiom.top/sympy/axiom.php?keyword=Discrete.*binomial&amp;regularExpression=true</a>
	表示搜索在同时包含discrete和binomial单词的定理。
</p>
<hr />
<br>
<h3>定理依存关系分析</h3>
<br>
<h4>上层定理引用关系</h4>
以下以
<a href='../axiom.php?module=Discrete.combinatorics.binomial.theorem'>牛顿二项式定理</a>
为例 ：
<br>
鼠标指向网页第一个超链接，会出现悬浮提示“callee hierarchy”。如图所示：
<img class=zoom src="png/hierarchy/hyperlink.png" />
<hr />
<br>
单击该超链接即可进入
<a
	href='../axiom.php?callee=axiom.Discrete.combinatorics.binomial.theorem'>上层定理引用层级图</a>
。如图所示：
<img class=zoom src="png/hierarchy/callee.png" />
<br>
以上结果显示有以下几个定理在论证过程中引用了二项式定理：
<ul>
	<li><a href='../axiom.php?module=Discrete.difference.factorial'>axiom.Discrete.difference.factorial</a></li>
	<li><a href='../axiom.php?module=Discrete.matrix.vandermonde.concatenate'>axiom.Discrete.matrix.vandermonde.concatenate</a></li>
</ul>
在“上层定理引用层级图”中单击>>>>(展开按钮)，可以进一步查看上层定理的更上一层定理。单击<<<<(隐藏按钮)，可以隐藏展开后的定理。
<br>
在“上层定理引用层级图”中单击
<a
	href='../axiom.php?callee=axiom.Discrete.combinatorics.binomial.theorem#deep'>callee</a>
超链接，可以展开所有上层定理引用关系图。如图所示：
<img class=zoom src="png/hierarchy/deep/callee.png" />
<hr />
<br>
<br>
<h4>下层定理引用关系</h4>

<br>
在“上层定理引用层级图”中单击
<a
	href='../axiom.php?caller=axiom.Discrete.combinatorics.binomial.theorem'>caller</a>
超链接，可以查看下层定理引用关系图。如图所示：
<img class=zoom src="png/hierarchy/caller.png" />
<hr />
以上结果显示在二项式定理的论证过程中引用了以下几个定理：
<ul>
	<li><a href='../axiom.php?module=Discrete.combinatorics.binomial.Pascal'>axiom.Discrete.combinatorics.binomial.Pascal</a>组合数学中的<a
		href='https://en.wikipedia.org/wiki/Pascal%27s_rule'>Pascal法则</a>，以法国数学家Pascal命名。</li>
	<li><a href='../axiom.php?module=Algebra.Imply.to.cond.induction'>axiom.Algebra.Imply.to.cond.induction</a>第一<a
		href='https://en.wikipedia.org/wiki/Mathematical_induction'>数学归纳法</a>，一种递归证明方法。</li>
</ul>
<br>

在“下层定理引用层级图”中单击
<a
	href='../axiom.php?caller=axiom.Discrete.combinatorics.binomial.theorem#deep'>caller</a>
超链接，可以展开所有下层定理引用关系图。如图所示：
<img class=zoom src="png/hierarchy/deep/caller.png" />
<hr />
<br>
<hr />
<br>
<br>
<h2>线下使用指南</h2>
线下使用该工具需要自己搭建本地php网站，具体php安装过程请参考安装部署文档
<a href='../php installation.docx'>php installation.docx</a>
。
在linux环境下使用以下命令安装：<br>
cd /usr/local<br>
git clone https://github.com/cosmosZhou/shell.git<br>
cd shell/php<br>
make<br>
sh start.sh port=80 DocumentRoot=/home/github<br>
DocumentRoot设定为所需的工程(网页)文件夹目录。<br>

线下使用还必须安装python开发环境。建议使用python3.9版的。
以下介绍python工程的使用方法：
<br>
<br>
以线下windows版为例，
<h4></h4>
<li>指定一个网页文件夹，比如：E:\github，按照php installation.docx所提供的方法，
	修改php网站的DOCUMENT_ROOT。然后进入该文件夹：<br>cd E:\github
</li>
<br>
<li>使用git下载python工程源代码： <br> git clone --depth=1 <a
	href=https://github.com/math-proof/lemma.git>https://github.com/math-proof/lemma.git</a>
</li>
<br>
<li>进入axiom文件夹：<br>cd axiom
</li>
<br>
<li>执行run命令，其中debug=1表示输出调试信息，debug=0表示不输出调试信息：<br>python run.py debug=1

</li>
<br>
<li>执行run完毕后会打印执行耗时，以及整个定理库的自动化证明的情况，比如， <br> in all 868 axioms<br>
	unproved:<br> (调试信息省略)....... <br> websites:<br> (调试信息省略)....... <br>
	seconds cost = 45.13455533981323<br> minutes cost =
	0.7522425889968872<br> total unproved = 22 <br> total failures = 0

</li>
<br>
<li>打开Chrome或者Edge/IE浏览器，在浏览器地址栏输入：<br> <a href='../axiom'>http://localhost/axiom/index.php</a>
	<br>即可启动软件网站可视化定理库，这样就可以在本地环境下直接访问可视化定理库了
</li>
<br>
<hr />
<br>