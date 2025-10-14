# What is axiom.top
  <br>
  
[axiom.top](../index.php) is a website for symbolic	semi-mechanized axiomatized theorem-proving system, consisting of two versions written respectively in Python and Lean language. The [Python](https://github.com/cosmosZhou/axiom/tree/master) version is based on open-source symbolic computation project of [sympy](https://github.com/sympy/sympy) and 
[Maxima](http://maxima.sourceforge.net), its main terminology is defined according to the naming conventions of the commercial algebraic system 
[Mathematica](https://reference.wolfram.com/language/index.html.en?source=footer). The [Lean](https://github.com/cosmosZhou/axiom/tree/main) version is translated from the Python version. It's main ideals are: semi-mechanization, axiomatization, and the pursuit of logic correctness. At present, it can be used in conducting semi-automatic proving for theorems from mathematics textbook.  

* the above-mentioned semi-mechanization is so defined that:   
at present, we can't devise a fully-automatic machine to process human-like logic reasoning steps in theorem-proving according the given prerequisites and conclusions.  
The machine can only solve the mathematical problem according the instruction provided by humans. Humans must tell the computer by searching through the axiom knowledge bank, what theorems or axioms to apply in front of a given mathematical problem. 
* the above-mentioned axiomatization is so defined that:  
every mathematical theorem, in the final analysis, can be proved by axioms which are unprovable, which are assumed self-evident, whose correctness is hypothesized by humans to hold true.  
The whole mathematical theorem knowledge bank is built step by step on these presumably true hypotheses.

* the above-mentioned pursuit of logic correctness is so defined that:  
during the processing of conducting reasoning, in accordance with the statements defined in 
[Hilbert's program](https://en.wikipedia.org/wiki/Hilbert%27s_program), the program strives to be logically valid within the grammars defined by [formal language](https://en.wikipedia.org/wiki/Formal_language).   
Each theorem is proved according to the assumptions and correctness of some previously proved theorems or axioms. In this project, each mathematical problem will be expressed as a [Python](https://www.python.org/), [Lean](https://lean-lang.org/) statement which is precisely defined with no ambiguity which can emerge when one use natural language to express a mathematical problem, such as evidently/conspicuously, likewise, equivalently, conversely, in summary/put it in a nutshell.   
One can easily locate the website information in the Google search engine: [定理库](https://www.google.com.hk/search?q=%E5%AE%9A%E7%90%86%E5%BA%93).  
In the open-source community, other automatic thoerem libraries include: [leanprover](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Algebra/Basic.html), [coq](https://github.com/coq/coq) and [isabelle](https://isabelle.in.tum.de/).

<br><br>
------


# The construction of Mathematical Theorem Repertoire
  <br>
  
As of this writing, <label id=count>____</label> theorems have been recored in the theorem repertoire, which can be applied in semi-mechanized axiomatized system of mathematical theorem proving.  
It is mainly comprising of :  	
	
* [Algebra](../?module=Algebra) refers to elementary Algebra, which mainly delves into equations transformation、symbol substitution techniques, finite series [∑ telescoping](../?module=Algebra.Sum.eq.Add.telescope.step)、∏ product telescoping, the property of transitivity for inequalities, solving [simple equations](../?module=Algebra.AndImpS_Eq.of.Add.eq.Zero.simple), [quadratic equations](../?module=Algebra.And_Imp_Or_EqS_Div.of.Add.eq.Zero.quadratic), [cubic equations](../?module=Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic) and [quartic equations](../?module=Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.quartic), [summation by parts](../?module=Algebra.Sum.eq.Add.by_parts), as well as the proof of [mathematical induction method](../?module=Bool.Eq_0.of.Eq_0.All_Imp);   
* [Set](../?module=Set) refers to Set theory, which is the core foundation of the theories of whole mathematical proving and analysis. It involves lots of propositions using the terminologies like 
ForAll, Exists, Element, Subset, for example: 
the proof of [inclusion-exclusion principle](../?module=Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion). It can be so said that: set theory is the fundamental grammar of automatic theorem proving.  
* [Trigonometry](../?module=Trigonometry) is comprised of identities of trigonometry: 
[addition principle of cosine](../?module=Trigonometry.CosSub.eq.AddSinSin_CosCos), [product principle of trigonometry](../?module=Trigonometry.MulSin_Cos.eq.AddDivSSin), and so on.   
* [Calculus](../?module=Calculus) comprises :   
[the definition of limit](../?module=Calculus.Any.All.of.Eq_Limit.limit_definition) and its fundamental theories which is the theoretical basis of Calculus.  
proof of [integration by parts](../?module=Calculus.Integral.eq.Add.by_parts);  
determination of some integral for certain transcendental functions;  
* [Discrete](../?module=Discrete) section is comprised of number theory, Discrete mathematics, combinatorics, linear Algebra, some basic counting techniques involving permutations, such as 
combinatoric induction for [second Stirling Number](../?module=Discrete.Stirling.eq.Add.recurrence),  
derivation for [Catalan Number](../?module=Discrete.Eq.of.Eq.Eq.catalan.recurrence)， 
basics of [continued fraction](../?module=Discrete.Add.eq.Pow.HK.recurrence); as well as the existence of [Cholesky decomposition](../?module=Discrete.Any.Eq.of.Eq_Adjoint.Imp_Gt_0.Cholesky).  
* [Probability](../?module=Probability) refers to statistics and probability theory, comprising: the derivation of the probability density formula of some common distribution (such as, binomial distribution, Gaussian distribution, poisson distribution, die distribution, Χ<sup>2</sup>distribution)，as well as propositions related to [Bayes theorem](../?module=Probability.Pr.eq.Div.Pr.bayes), and the [law of large numbers](../?module=Probability.Eq.Limit.Pr.of.Eq_Conditioned.Eq_Expect.Eq_Var.law_of_large_numbers);  
* [Tensor](../?module=Tensor) section is related to the mathematical theories behind the contemporary deep learning / machine learning techniques, including the mathematical modeling used in natural language processing / understanding, formulae deduction or proof of
[LSTM](../?module=Tensor.Eq.of.Eq.Eq.long_short_term_memory),
[GRU](../?module=Tensor.Eq_AddMulS.gated_recurrent_unit),
[CNN](../?module=Tensor.Eq.of.Eq_Stack_Bool_In.conv1d),
[BERT](../?module=Tensor.DotSoftmax.eq.Stack_Div.scaled_dot_product_attention),
[GPT](../?module=Tensor.DotSoftmax.eq.Stack_Dot.gpt),
Conditional Random Field [CRF](../?module=Tensor.And.of.Ne_0.Eq.Eq.Eq.crf.y_given_x),
KMeans [clustering convergence](../?module=Set.LeAddSSumS_SquareSub_Sum.of.In.NotIn.LeAbsSSub_Sum), [General Rotary Position Embedding](../?module=Tensor.Dot.eq.Add.of.Eq_Mul.Eq_Mul.Eq_Block.position_representation.plane) for Vision Transformer, [Policy Gradient Theorem](../?module=Tensor.EqDot_GradExpect.of.Eq_Conditioned.Eq_Expect.IsFinite.IsFinite.unbiased_advantage_estimate) from Reinforcement Learning. 
Probability theory provides the fundamental theoretical basis for machine learning so that this contemporary technique can be  explainable.  

<br><br>
-------
This newly emerged semi-mechanized axiomatized theorem-proving system can simplify reasoning steps in mathematical analysis, thus achieving the ideal of "plugging in the dynamos of thinking". The researcher need only master the macro skeleton of reasoning, leaving the detailed computation to computer. It can be applied for theoretical mathematical proving, which can be useful in providing reference or guidance during the course of mathematical analysis for algorithm engineers, researcher in their research work. It can also be used for mathematical researchers to manage and edit their theoretical papers, without the need of manual editing of mathematical formulae since the latex printing is automatically generated by programming. One Can even use the on-line Integrated Development Environment (IDE) for [Python](https://www.python.org/) to edit the mathematical theorems to finish theoretical research work. The on-line [Python](https://www.python.org/) IDE provides a powerful hotkey F3 for users to locate the definition of any symbol or function instantly. It is of practical use for theoretical research, industrial research or pedagogical purposes. It is a mathematical textbook written in Python Language, as well as an on-line reference book for both mathematical theorems and algorithmic models for industry.
<br><br>

<script type=module>
	$('#count').innerHTML = await get("../php/request/count.php");
</script>