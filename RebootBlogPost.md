\documentclass[pra,floatfix,
amsmath,superscriptaddress, 12pt]{article}
\usepackage{color}
\usepackage{mathtools}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
%\usepackage{palatino}
\usepackage{layout}
\usepackage{amsmath}
\usepackage{amsthm}
%\usepackage{amsfonts}
\usepackage{amssymb}
\usepackage{amscd}
\usepackage{enumerate,bbm}
\usepackage{latexsym, graphics, graphicx, epsfig, bm}
\usepackage{esvect}
\usepackage{verbatim}
\usepackage{lipsum}
\usepackage{caption}
\usepackage{subcaption}
\usepackage[all]{xy}
\usepackage{xfrac}   
\usepackage{prftree}
\usepackage{braket}
\usepackage{mathpartir}

\usepackage{tikz}
\usetikzlibrary{arrows,shapes,snakes,automata,backgrounds,petri,positioning}

\usepackage{setspace}
\doublespacing

%Tikz commands
\usetikzlibrary{shapes,snakes}
\usetikzlibrary{shapes,shapes.geometric,shapes.misc}
\pgfdeclarelayer{edgelayer}
\pgfdeclarelayer{nodelayer}
\pgfsetlayers{edgelayer,nodelayer,main}

\tikzstyle{none}=[inner sep=0pt]
\tikzstyle{port}=[inner sep=0pt]
\tikzstyle{component}=[circle,fill=white,draw=black]
\tikzstyle{integral}=[inner sep=0pt]
\tikzstyle{differential}=[inner sep=0pt]
\tikzstyle{codifferential}=[inner sep=0pt]
\tikzstyle{function}=[regular polygon,regular polygon sides=4,fill=white,draw=black]
\tikzstyle{function2}=[regular polygon,regular polygon sides=4,fill=white,draw=black, inner sep=1pt]
\tikzstyle{duplicate}=[circle,fill=white,draw=black, inner sep=1pt]
\tikzstyle{wire}=[-,draw=black,line width=1.000]
\tikzstyle{object}=[inner sep=2pt]
%\input{NuiokStyle.tikzstyles}


\usepackage{tikz-cd}

\usepackage[margin=.5in]{geometry}

\usepackage{ mathrsfs }
\usepackage{physics}

%\setlength\parindent{0pt}
%\setlength{\parskip}{1em}


%\usepackage[round]{natbib}
%\bibliographystyle{natbib-oup}



\newtheorem{thm}{Theorem}
\theoremstyle{definition}


\newtheorem{df}[thm]{Definition}
\newtheorem{defn}[thm]{Definition}
\newtheorem*{df*}{Definition}
\newtheorem{prop}[thm]{Proposition}
\newtheorem{cor}[thm]{Corollary}
\newtheorem{ex}[thm]{Example}
\newtheorem{rem}[thm]{Remark}
\newtheorem*{rem*}{Remark}
\newtheorem{lem}[thm]{Lemma}
\newtheorem*{lem*}{Lemma}
\newtheorem{obs}[thm]{Observation}


\newtheorem{theorem}[thm]{Theorem}
\newtheorem*{theorem*}{Theorem}
\newtheorem{proposition}[thm]{Proposition}
\newtheorem{lemma}[thm]{Lemma}
\newtheorem{conjecture}[thm]{Conjecture}
\newtheorem{corollary}[thm]{Corollary}
\newtheorem{definition}{Definition}
\newtheorem*{remark}{Remark}
\newtheorem*{example}{Example}


\newcommand{\N}{\mathbb{N}}
\newcommand{\R}{\mathbb{R}}
%\newcommand{\cD}{\mathbf{D}}
\newcommand{\cC}{\mathbf{C}}
\newcommand{\obC}{\mathsf{Ob}(\mathbf{C})}
\newcommand{\obD}{\mathsf{Ob}(\mathbf{D})}
\newcommand{\Tst}{T(s\leq t)}
\newcommand{\LAst}{\overleftarrow{A}(s\leq t)}
\newcommand{\RAst}{\overrightarrow{A}(s\leq t)}
%\newcommand{\id}{\id}



\newcommand{\C}{\mathbb{C}}
\newcommand{\I}{\mathbb{I}}
\newcommand{\h}{\mathcal{H}}
\newcommand{\F}{\mathcal{F}}
\newcommand{\W}{\mathcal{W}}
\newcommand{\E}{\mathcal{E}}
\newcommand{\Oo}{\mathcal{O}}
\newcommand{\B}{\mathcal{B}}
\newcommand{\p}{\mathcal{P}}
\newcommand{\liso}{\overset{\sim}{\longrightarrow}}

\DeclareMathOperator{\NICM}{\mathrm{NICM}\;}
\DeclareMathOperator{\ICM}{\mathrm{ICM}\;}
\DeclareMathOperator{\POVM}{\mathrm{POVM}\;}


\DeclareMathOperator{\bmath}{\boldsymbol}
\DeclareMathOperator{\cone}{\mathrm{cone}}
\DeclareMathOperator{\coker}{\mathrm{coker}}
\DeclareMathOperator{\Pos}{\mathrm{Pos}\;}
\DeclareMathOperator{\one}{\mathbbm{1}}
\DeclareMathOperator{\Prok}{\text{Proj}}



\DeclareMathOperator{\ra}{\rightarrow}
\newcommand{\xra}[1]{\xrightarrow{#1}}
\newcommand{\xto}[1]{\xrightarrow{#1}}

%macros for free prop section
\newcommand{\fF}{\mathfrak{F}}
\newcommand{\cG}{\mathcal{G}}
\newcommand{\cR}{\mathcal{R}}
\newcommand{\cD}{\mathcal{D}}
\newcommand{\Ob}{\mathsf{Ob}}
\newcommand{\evmap}{\mathsf{ev}}
\newcommand{\coev}{\mathsf{coev}}
\newcommand{\bigslant}[2]{{\raisebox{.2em}{$#1$}\left/\raisebox{-.2em}{$#2$}\right.}}

%circled number obsession
\newcommand*\circled[1]{\tikz[baseline=(char.base)]{
            \node[shape=circle,draw,inner sep=2pt] (char) {#1};}}



%\newcommand{\braket}[3]{\langle #1|#2|#3\rangle}
%inner product
%\newcommand{\ip}[2]{\langle #1|#2\rangle}
%outer product
%\newcommand{\op}[2]{|#1\rangle \langle #2|}
%\newcommand{\slocc}{\overset{\underset{\mathrm{SLOCC}}{}}{\longrightarrow}}
%\newcommand{\N}{\mathbb{N}}
%\DeclareMathOperator{\tr}{Tr}
\DeclareMathOperator{\conv}{conv}
\DeclareMathOperator{\projset}{\mathbb{P}}
\DeclareMathOperator{\union}{\mathbb{U}}
\newcommand{\mc}[1]{\mathcal{#1}}
\newcommand{\mbf}[1]{\mathbf{#1}}
\newcommand{\mbb}[1]{\mathbb{#1}}
\newcommand{\CP}{\text{CP}}
\newcommand{\dep}{\mathcal{D}}
\newcommand{\aLOCC}{\overline{\text{LOCC}}}
\newcommand{\mrm}[1]{\mathrm{#1}}
\newcommand{\msf}[1]{\mathsf{#1}}
\newcommand{\U}{\overset{\underset{\text{NICM}}{}}{\longrightarrow}}
%\newcommand{\ol}[1]{\overline{#1}}

\newcommand{\proj}{\text{Proj}}

\DeclareMathOperator{\LOCC}{LOCC}
\DeclareMathOperator{\LOCCN}{LOCC_{\N}}
\DeclareMathOperator{\SEP}{SEP}


\DeclareMathOperator{\pre}{\normalfont\text{pre}}
\DeclareMathOperator{\post}{\normalfont\text{post}}
\DeclareMathOperator{\id}{{\normalfont\text{id}}}

\DeclarePairedDelimiter\name{\ulcorner}{\urcorner}
\DeclarePairedDelimiter\coname{\llcorner}{\lrcorner}

\newcommand{\no}[1]{$^{#1}$}

%\setlength\parindent{0pt}


\author{Nuiok Dicaire and Paul Lessard}
\date{Elsewhen}

\begin{document}

Shulman's Practical Type Theory for Symmetric Monoidal Categories

*guest post by [Nuiok Dicaire](https://www.inf.ed.ac.uk/people/students/Nuiok_Dicaire.html) and [Paul Lessard](https://sites.google.com/view/paul-roy-lessard/)*




Many well-known type theories, Martin-L\"{o}f dependent type theory or linear type theory for example, were developed as syntactic treatments of particular forms of reasoning. Constructive mathematical reasoning in the case of Martin-L\"{o}f type theory and resource dependent computation in the case of linear type theory. It is after the fact that these type theories provide convenient means to reason about locally Cartesian closed categories or $\star$-autonomous ones. In this post, a long overdue part of the Applied Category Theory Adjoint School (2020!?), we will discuss a then recent paper by Mike Shulman, 
\textit{A Practical Type Theory for Symmetric Monoidal Categories}, where the author reverses this approach. 
Shulman starts with symmetric monoidal categories as the intended semantics and then (reverse)-engineers a syntax in which it is \emph{practical} to reason about such categories.

\hrulefill

Which properties of a type theory (for symmetric monoidal categories) make it practical? Shulman, synthesizing various observations, and settles on a few basic {\color{red}tenets} to guide the invention of the syntax and its interpretation into symmetric monoidal categories. We reduce these further to the conditions that the type theory be: (1) intuitive, (2) concise, and (3) complete.

\paragraph{Intuitive} First, a practical type theory should permit us to leverage our intuition for reasoning about "sets with elements". What this means in practice is that we require a "natural deduction style" type theory, in which contexts look and feel like choosing elements, and typing judgements look and feel like functions of sets. Moreover, we also require an internal-language/term-model relationship with symmetric monoidal categories which provide correspondences:
\begin{eqnarray*}
\textbf{Category}              &  & \textbf{Type Theory}\\
\mathrm{objects}                & \longleftrightarrow & \mathrm{contexts, (types)}\\
\mathrm{morphisms}              & \longleftrightarrow & \mathrm{typing\ judgments}\\
\mathrm{commuting\ diagrams}     & \longleftrightarrow & \mathrm{equality\ judgments}
\end{eqnarray*}


\paragraph{Concise} When stripped of the philosophical premises of what terms, types, judgements etc. are, the rules of a type theory can be seen to generate its derivable judgments. It is therefore desirable that the translation between symmetric monoidal categories and the rules of their associated type theories proceed by way of the most concise combinatorial description of symmetric monoidal categories possible.

\paragraph{Complete} Lastly we ask that, given a presentation for a symmetric monoidal category, the type theory we get therefrom should be complete. By this, we mean that a proposition should hold in a particular symmetric monoidal category if and only if it is derivable as a judgment in the associated type theory.

\section{Symmetric Monoidal Categories and Presentations of \textsf{PROP}s}

While it is well-known that every symmetric monoidal category is equivalent
to a symmetric \emph{strict} monoidal category, it is probably less well-known that every symmetric strict monoidal category is equivalent to
a \textsf{PROP}.

\begin{definition} A \textsf{PROP}, $\mathfrak{P}=(\mathfrak{P},\mathbf{P})$, consists of a set $\mathbf{P}$ of generating objects and a symmetric strict monoidal category $\mathfrak{P}$ whose underlying monoid of objects is the free monoid on the set $\mathbf{P}$.
\end{definition}

This is not however too hard to see: the equivalence between \textsf{PROP}s and symmetric monoidal categories simply replaces every equality of objects $A\otimes B = C$ with an isomorphism $A \otimes B \overset{\sim}{\longrightarrow} C$, thereby rendering the monoidal product to be free. We will develop what we mean by presentation over the course of a few examples. In doing so we hope to give the reader a better sense for \textsf{PROP}s.

\begin{example}
Given a set $\mathbf{X}$, let $\Sigma_{\mathbf{X}}$ be the \textbf{free permutative category on} $\mathbf{X}$. This is a symmetric monoidal category whose monoid of objects is the monoid of lists drawn from the set $\mathbf{X}$ and whose morphisms are given by the expression
\[
    \Sigma_{\mathbf{X}}\left(\overrightarrow{X},\overrightarrow{Y}\right)
    =
    \Set{\sigma \in S_{n} | \overrightarrow{X_\sigma}=\overrightarrow{Y}}
\]
(where by $\overrightarrow{X_\sigma}$ we mean the reorganization of the list $\overrightarrow{X}$ according to the permutation $\sigma$). For every set $\mathbf{X}$, $\Sigma_{\mathbf{X}}$ is a \textsf{PROP}.
\end{example}

\begin{example} For a more complicated example, let $\mathbf{X}_0$ be a set and let
\[
    \mathbf{X}_1
    =
    \Set{(f_i,\overrightarrow{X}_i,\overrightarrow{Y}_i)}_{i\in I}
\]
be a set of triples comprised of names $f_i$ and pairs of lists $(\overrightarrow{X}_i,\overrightarrow{Y}_i)$ valued in $\mathbf{X}_0$. Let $F(\mathbf{X}_1,\mathbf{X}_0)$ denote the free symmetric monoidal category generated by $\Sigma_{\mathbf{X}_0}$ together with additional arrows $f_{i}:\overrightarrow{X}_i \longrightarrow \overrightarrow{Y}_i$ for each $i\in I$. Then $F(\mathbf{X}_1,\mathbf{X}_0)$ is also a $\msf{PROP}$.

%(We'll play fast and loose with the form of elements of these sets $\mathbf{X_1}$ later on, failing to distinguish between the name $f_i$ and the element $(\overrightarrow{X_i},\overrightarrow{Y_i})$)
\end{example}

Importantly, this second example is very nearly general - every \textsf{PROP} admits a bijective-on-objects and full, but not in general faithful, functor from some \textsf{PROP} of the form $F(\mathbf{X}_1,\mathbf{X}_0)$.

\begin{example}
 Let  $\mathbf{X}_0$ and $\mathbf{X}_1$ be as in the previous example and let
 \[
    \mathbf{R}=\Set{ (s_j,t_j) \in \mathsf{Mor}(F(\mathbf{X}_1,\mathbf{X}_0))^2 | j \in J}
 \]
 be a set of pairs of morphisms in the $\mathsf{PROP}$ $F(\mathbf{X}_1,\mathbf{X}_0)$. Let $F(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$ be the quotient of the symmetric monoidal category $F(\mathbf{X}_1,\mathbf{X}_0)$ by the congruence generated by $R \subset \mathsf{Mor}(F(\mathbf{X}_1,\mathbf{X}_0)) \times \mathsf{Mor}(F(\mathbf{X}_1,\mathbf{X}_0))$.
\end{example}

This last example is fully general. Every $\mathsf{PROP}$, hence every symmetric monoidal category, is equivalent to a $\mathsf{PROP}$ of the form $F(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$.

\begin{remark} If (generalized) computads are familiar, you may notice that our three examples here are free $\mathsf{PROP}$s on $0$, $1$, and $2$-computads.
\end{remark}

\section{From Presentations to Type Theories}

It is from these presentations $(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$ of $\mathsf{PROP}$s that we will build type theories $\mathsf{PTT}_{(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)}$ for the symmetric monoidal categories $F(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$. Indeed, reading $\rightsquigarrow$ as ``gives rise to'', we will see:
    \begin{eqnarray*}
      \mathbf{Generators}
        &
            &
            \mathbf{Judgments}
                \\
      \mathbf{X}_0
        & \xymatrix@C=3em{{}\ar@{~>}[r]&{}}
            & \mathrm{contexts} \\
      \mathbf{X}_1 & \xymatrix@C=3em{{}\ar@{~>}[r]&{}} & \mathrm{typing \ judgments} \\
      \mathbf{R}   & \xymatrix@C=3em{{}\ar@{~>}[r]&{}} & \mathrm{equality \ judgment}
    \end{eqnarray*}

\subsection{Contexts}

The contexts (usually denoted $\Gamma,\;\Delta$, etc.) of the type theory $\mathsf{PTT}_{(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)}$  are lists
    \[
        x_{1}:A_{1},\dots,x_{n}:A_{n}
    \]
of typed variables, where the $A_i$ are elements of the set $\mathbf{X}_{0}$. It's not hard to see that, up to the names of variables, contexts are in bijection with $\mathsf{List}(\mathbf{X}_0)$.

\subsection{Typing Judgments}

As promised, typing judgments correspond to morphisms in $F(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$. Here are some examples of morphisms and their corresponding judgements:
%
% \begin{eqnarray*}
%     \mathbf{Typing \ judgments}
%         &
%         %blank
%           &
%           \mathbf{Morphisms} \\
%     x:A\vdash f\left(x\right):B
%         &
%         \longleftrightarrow
%             & f:(A) \longrightarrow (B) \\
%     x:A\vdash\left(h_{\left(1\right)}\left(x\right),h_{\left(2\right)}\left(x\right)\right):B
%         &
%         \longleftrightarrow
%             &
%             h:(A)\longrightarrow\left(B_{1},B_{2}\right) \\
%     \vdash\left(|z^{a}\right):\left(\right)
%         &
%         \longleftrightarrow
%             &
%             z:() \longrightarrow ()
% \end{eqnarray*}
\begin{eqnarray*}
    \mathbf{Morphisms}
        &
        %blank
          &
          \mathbf{Typing \ judgments} \\
    f:(A) \longrightarrow (B)
        &
        \longleftrightarrow
            &  x:A\vdash f\left(x\right):B
                \\
    %x:A\vdash\left(h_{\left(1\right)}\left(x\right),h_{\left(2\right)}\left(x\right)\right):B
    h:(A)\longrightarrow\left(B_{1},B_{2}\right)
        &
        \longleftrightarrow
            &
            x:A\vdash\left(h_{\left(1\right)}\left(x\right),h_{\left(2\right)}\left(x\right)\right):B
                \\
    z:() \longrightarrow ()
        &
        \longleftrightarrow
            &
            \vdash\left(|z^{a}\right):\left(\right)
\end{eqnarray*}

The rules from which these judgments may be derived correspond, roughly speaking, to applying a tensor product of generating morphisms in $\mathbf{X}_1$ composed with a braiding - something along the lines of:
\[
    \inferrule
    {\Gamma \dashv ( \overrightarrow{m}, \dots ,\overrightarrow{n} | \overrightarrow{z}) : ( \overrightarrow{A}, \dots, \overrightarrow{B}) \\
    (f:\overrightarrow{A} \rightarrow \overrightarrow{F}) \in \mathbf{X}_1 \\
    \cdots \\
    (g:\overrightarrow{B} \rightarrow \overrightarrow{G}) \in \mathbf{X}_1 \\
    ( \sigma : (\overrightarrow{F},\dots, \overrightarrow{G}) \rightarrow \bigtriangleup) \in \Sigma_{\mathbf{X}_0}
    }
    {\Gamma \dashv ( \sigma ( \overrightarrow{f}(\overrightarrow{m}),\dots,\overrightarrow{g}( \overrightarrow{n}) ) ) : \bigtriangleup}
\]
in which:
\begin{itemize}
	\item $\Gamma$ is a context, and $\Delta$ is a (list of) type(s);
	\item $\overrightarrow{m}, \dots ,\overrightarrow{n}$ are terms of types $\overrightarrow{A}, \dots , \overrightarrow{B}$ respectively;
	\item the $f$ through $g$ are generating arrows in the set $\mathbf{X}_1$; and
	\item $\sigma$ is the avatar in $\Sigma_{\mathbf{X}_0}$ of some permutation.
\end{itemize}
%
Now, it is rather clear that we are hiding something - the gory details of the rules from which the typing judgments are derived (the so-called identity and generator rules in Shulman's paper). However, the reader should rest assured that not only are the details not that onerous, but the more naive structural rules corresponding to tensoring,         composition, and braiding are admissible. In practical terms, this means that one is simply free to work with these more intuitive rules.




\subsection{Equality judgments}

Equality judgments, for example something of the form $x:A\vdash f\left(x\right)=h\left(g\left(x\right)\right):B,$ which in categorical terms corresponds to a diagram
%
\begin{eqnarray*}
    \vcenter{
                \vbox{
                    \xymatrix{
                        A
                        \ar[r]^{g}
                        \ar[dr]_{h}
                            &
                            (B)
                            \ar[d]^{f}
                                \\
                        %empty
                            &
                                (C)}}}
\end{eqnarray*}
%
%\begin{eqnarray*}
%    \mathbf{Commuting \ Diagrams}
%        &
%        %empty
%            &
%            \mathbf{Equality \ judgments}
%                \\
%    \vcenter{
%                \vbox{
%                    \xymatrix{
%                        A
%                        \ar[r]^{g}
%                        \ar[dr]_{h}
%                            &
%                            (B)
%                            \ar[d]^{f}
%                                \\
%                        %empty
%                            &
%                                \left( C \right)}}}
%        &
%        \longleftrightarrow
%            &
%            x:A\vdash f\left(x\right)=h\left(g\left(x\right)\right):B
%\end{eqnarray*}
%
are similarly derived from rules coming from the set $\mathbf{R}$. We will be more explicit later on within the context of an example.

\section{How do Symmetric Monoidal Categories fit into all this?}


%Below we will illustrate the type theory with an example and describe Shulman's type theoretical proof of the cyclicity of the trace in the practical type theory for the free dual pair. Before we do so however we'll expound on what is perhaps the central insight of Shulman's paper.
Until this point it is not actually terribly clear what makes this type theory specifically adapted to symmetric monoidal categories as opposed to Cartesian monoidal categories. After all, we have written contexts as lists precisely as we would write contexts in a Cartesian type theory. 
%
%
Although we may not always think about it, we write contexts in Cartesian type theories as lists of typed variables because of the universal property of the product - a universal property characterized in terms of projection maps. Indeed, in a Cartesian type theory lists can be recovered from the list of their projections. This is not the case for arbitrary symmetric monoidal products; in general there are no projection maps. And, even when there are, there is no guarantee that they have a similar computation rule (the type theoretic avatar of a universal property).

%  (for the cognoscenti we have $\beta$-rules

% \[
%     \mathsf{pr}_{1}\left( \mathsf{pair}\left(x,y\right)\right) = x
%     \quad \textrm{and} \quad
%     \mathsf{pr}_{2}\left( \mathsf{pair}\left(x,y\right)\right) = y
% \]
% and an $\eta$-rule
% \[
%     z=\mathsf{pair}\left(
%         \mathsf{pr}_{1}\left( z \right),
%         \mathsf{pr}_{2}\left( z \right)
%         \right)
% \] for (binary) cartesian products, however in general projection maps don't exist and the characterization of terms is not so straightforward)

To illustrate this in a mathematical context, consider a pair of vector spaces $U_1$ and $U_2$. Any element $z\in U_1 \times U_2$ of the Cartesian product of $U_1$ and $U_2$ is uniquely specified by the pair of elements $\mathsf{pr}_{1}(z) \in U_1$ and $\mathsf{pr}_{2}(z)\in U_2$ - $z=(\mathsf{pr}_1(z),\mathsf{pr}_2(z))$. However, elements of the tensor product $U_1 \otimes U_2$ need not be simple tensors of the form $x \otimes y$ and instead are generally linear combinations $\sum_{i=1}^{k}x_{1,i} \otimes x_{2,i}$ of simple tensors.

Provided we are careful however - meaning we do not perform any "illegal moves" in a sense we will make clear - we can still use lists. This is what Shulman does in adapting Sweedler's notation. Consider a general element
%
    \[
        \sum_{i=1}^{k}x_{1,i}\otimes x_{2,i} \in U_1 \otimes U_2
    \]
In Sweedler's notation this is written as $(x_{(1)}, x_{(2)})$ with the summation, indices, and tensor symbols all dropped. Provided we make sure that any expression in which $(x,y)$ appears is linear in both variables, this seeming recklessness introduces no errors.

To see how this plays out, suppose that we have a morphism $f$ with domain $A$ and co-domain being the tensor product $(B_1,...,B_n)$. In Shulman's adaptation of Sweedler's notation this corresponds to the judgment:
%
\[
a:A\vdash\left(f_{\left(1\right)}\left(a\right),\dots,f_{\left(n\right)}\left(a\right)\right):\left(B_{1},\dots,B_{n}\right)
\]
%

Importantly, our typing rules will never derive the judgment $a:A\dashv f_{(k)}:B_k$ and we will only be able to derive $a:A \dashv \mathsf{pr}_k\left(f_{\left(1\right)}\left(a\right),\dots,f_{\left(n\right)}\left(a\right)\right):B_k$ if we have $\mathsf{pr}_k:(B_1,\dots,B_n) \rightarrow B_k$ in $\mathbf{X}_1$ and more, unless $\mathbf{R}$ specifies that $\mathsf{pr}_k$ acts like a projection, $\mathsf{pr}$ is but a name.

Since this type theory allows us to pretend, in a sense, that types are ``sets with elements'', the symmetric monoidal aspect of the type theory can be moralized as:
\begin{itemize}
    \item terms of product types are not-necessarily-decomposable tuples;
\end{itemize}
whereas in a Cartesian ``sets with elements'' style type theory:
\begin{itemize}
    \item terms of product types are decomposable tuples.
\end{itemize}

\begin{remark}
Taking a hint from the bicategorical playbook can give us a more geometric picture of the difference between an indecomposable tuple and a decomposable one. Since every symmetric monoidal category is also a bicategory with a single object, a typed term, usually a $1$-cell, also corresponds to $2$-cells between (directed) loops. In this vein we may think of an indecomposable tuple $(x_{(1)},x_{(2)},\dots,x_{(n)}):\overrightarrow{A}$ as an $n$-sphere in $\overrightarrow{A}$ whereas a decomposable one, say $(x,y,\dots,z):\overrightarrow{A}$, corresponds to a torus (of some dimension) in  $\overrightarrow{A}$.
\end{remark}

% \begin{remark}
% 	The purpose of the parentheses around the subscripts is to remind us that we cannot treat the $x_{(k)}$ individually - a priori $(x_{(1)},\dots,x_{(n)})$ is not decomposable into a list - and {\color{red} to separate the subscripts of typed terms
%         \[
%             (x_{(i_1)},\dots,x_{(i_n)}):(X_1,\dots,X_n)
%         \]
%     from the subscripts of their types.  What?}
% \end{remark}

%The rules for this typing judgment will formalize, for general symmetric monoidal categories, the way in which we could pretend above that every element of a tensor product of vector spaces was a simple tensor provided we only ever considered expressions which were linear in each variable.





% The typing judgments of $\mathsf{PTT}_{\langle G|R\rangle}$ are
% derived from rules specified by the generating
% formal morphisms of the signature $\mathcal{G}$. For example, if
% in the signature $\mathcal{G}$ we find a formal morphism
% $$ f:\left(A_{1},\dots,A_{m}\right)\longrightarrow\left(B_{1},\dots,B_{n}\right)$$ 
% then, we will have a rule for the typing judgment which corresponds to applying that morphism to a list  $\left(M_{1},\dots,M_{n}\right):\left(A_{1},\dots,A_{n}\right)$ of typed terms.

%Lastly, it is worth to mention a few words about the other two kinds of rules of deriveable judgments that appear in this type theory.
% As we have already mentioned, the typing judgments are
% derived from rules specified by the arrows of the signature $\cG$. For example, if
% in the signature $\mathcal{G}$ we find a formal morphism
% $$ f:\left(A_{1},\dots,A_{m}\right)\longrightarrow\left(B_{1},\dots,B_{n}\right)$$
% then we have a rule for the typing judgment which corresponds to
% applying that morphism to a list of typed terms $\left(M_{1},\dots,M_{n}\right):\left(A_{1},\dots,A_{n}\right)$.
% %
%Concerning the rules for the equality judgment, they are simply written as to assert the generating identities as axioms and build a congruence from them.


% All we really need 

%  we then denote maps into arbitrary
% tensor products as follows. 
% \[
% \xymatrixrowsep{0pc}
% \xymatrix{
%                 A\ar[r]^{f} & \left(B_{1},\dots,B_{n}\right)\\
% a\ar@{|->}[r] & \left(f_{\left(1\right)}\left(a\right),\dots,f_{\left(n\right)}\left(a\right)\right)
% }
% \]



%Now, for a variety of reasons, we cannot simply bend some cartesian type theory to our will to develop a practical type theory for symmetric monoidal categories. Perhaps chief among these reasons is that while the product enjoys a universal property characterized in terms of projection maps, the same cannot be said of symmetric monoidal products in general. Indeed, the universal properties of many monoidal products of interest, co-products, tensor products of algebras, etc. are characterized in terms of co-projection maps.

%\par

%Consider the category $\mathsf{Vect}_{\mathbf{R}}$ of real vector spaces. In that category, for any objects $X$ and $Y$ we have that any element  $z\in X \times Y$ is uniquely specified by a pair of elements $x\in X$ and $y\in Y$. 
%We have both that, for every $x \in X$ and $y \in Y$,

%However, in general, for the tensor product $X\otimes Y$ not only do we not have access to projection maps, but what is more, a general element $z\in X \otimes Y$ need not be of the form $x\otimes y = \mathsf{pair}\left(x,y\right)$.%; not every vector in a tensor product of vector spaces is a simple tensor, instead they are linear combinations of such.


% Consider that the co-multiplication of a co-algebra in vector spaces may be written
% elementarily as follows.
% \[
%     \xymatrixrowsep{0pc}
%     \xymatrix{C\ar[r]^{\Delta} & C\otimes C\\
%         c\ar@{|->}[r] & \sum_{i=1}^{k}c_{\left(1\right)}^{i}\otimes c_{\left(2\right)}^{i}
%     }
% \]
% Sweedler long ago noted that it was convenient to drop summation and
% even to drop indices. Going further and replacing $\left(\_\right)\otimes\cdots\otimes\left(\_\right)$
% with $\left(\_,\dots,\_\right)$, both in the formation of tensor
% products and for 'simple tensors', we then denote maps into arbitrary
% tensor products as follows. 
% \[
% \xymatrixrowsep{0pc}
% \xymatrix{
%                 A\ar[r]^{f} & \left(B_{1},\dots,B_{n}\right)\\
% a\ar@{|->}[r] & \left(f_{\left(1\right)}\left(a\right),\dots,f_{\left(n\right)}\left(a\right)\right)
% }
% \]

%***************************************************************************************************************************************

% This notation then informs Shulman's term formation rules: for example%\footnote{For expository purposes we've replaced $f\in\mathcal{G}\left(A_{1},\dots,A_{m};B_{1},\dots,B_{m}\right)$,
% %which is the hypothesis that $f$ is a \emph{generating} morphism,
% %with the more general hypothesis that $f\in \mathsf{Hom} \left(A_{1},\dots,A_{m};B_{1},\dots,B_{n}\right)$.} 
% \[
% \frac{\begin{array}{c}
% \Gamma\vdash M_{1}\ \mathsf{term}\dots\Gamma\vdash M_{m}\ \mathsf{term}\\
% f\in\mathsf{Hom}\left(A_{1},\dots,A_{m};B_{1},\dots,B_{n}\right)\ m\geq1\ n\geq2\ 1\leq k\leq n
% \end{array}}{\Gamma\vdash f_{\left(k\right)}\left(M_{1},\dots,M_{m}\right)}
% \]
% which in the case $m=1$ and $\Gamma\vdash a\ \mathsf{term}$ allows
% us to form the bare terms $f_{\left(k\right)}\left(a\right)$ as in
% Sweedler's notation and then the rules for our typing judgments will allow us to derive 
% \[
% a:A\vdash\left(f_{\left(1\right)}\left(a\right),\dots,f_{\left(k\right)}\left(a\right)\right):\left(B_{1},\dots,B_{n}\right)
% \]
% the typing judgment which corresponds to the morphism $f$. The rules for this typing judgment will formalize, for general symmetric monoidal categories, the way in which we could pretend above that every element of a tensor product of vector spaces was a simple tensor provided we only ever considered expressions which were linear in each variable.





% \subsubsection{Rules for the term judgment}

% The term judgments of $\mathsf{PTT}_{\langle\mathcal{G}|\mathcal{R}\rangle}$
% are derived by way of rules combining Sweedler's notation and the
% generating morphisms of the signature $\mathcal{G}$, for example
% we have the rule
% \[
% \frac{\begin{gathered}\Gamma\vdash M_{1}\quad\dots\quad\Gamma\vdash M_{n}\\
% f\in\mathcal{G}\left(A_{1},\dots,A_{m};B_{1},\dots,B_{n}\right)\quad m\geq1\quad n\geq2\quad1\leq k\leq n
% \end{gathered}
% }{\Gamma\vdash f_{\left(k\right)}\left(M_{1},\dots,M_{n}\right)\ \mathsf{term}}
% \]
% which permits us to form the term $f_{\left(k\right)}\left(M_{1},\dots,M_{n}\right)$
% which corresponds to the $k^{th}$ Sweedler component of a morphism
% \[
% f:\left(A_{1},\dots,A_{m}\right)\longrightarrow\left(B_{1},\dots,B_{n}\right)
% \]
%  in the signature $\mathcal{G}$. When the generator $f$ has nullary
% domain, we introduce a subtly different term formation rule which
% add labels drawn from an alphabet $\mathfrak{A}$, syntactic sugar
% which Shulman uses to great effect later on.

% \[
% \frac{\begin{gathered}\\
% f\in\mathcal{G}\left(;B_{1},\dots,B_{n}\right)\quad\mathfrak{a}\in\mathfrak{A}\quad n\geq2\quad1\leq k\leq n
% \end{gathered}
% }{\Gamma\vdash f_{\left(k\right)}^{\mathfrak{a}}\ \mathsf{term}}
% \]

%***************************************************************************************************************************************
% \subsubsection{Rules for the typing judgment}

% The typing judgments of $\mathsf{PTT}_{\langle G|R\rangle}$ are
% derived from rules specified by the elements of $G_{1}$, the generating
% formal morphisms of the signature $\mathcal{G}$. For example, if
% in the signature $\mathcal{G}$ we find a formal morphism
% \[
% f:\left(A_{1},\dots,A_{m}\right)\longrightarrow\left(B_{1},\dots,B_{n}\right)
% \]
%  then, we've a rule for the typing judgment which corresponds to
% applying that morphism to a list of typed terms $\left(M_{1},\dots,M_{n}\right):\left(A_{1},\dots,A_{n}\right)$.
% The foreboding vaguery will be addressed shortly.

% \subsubsection{Rules for the equality judgment}

% Lastly, the rules for the equality judgment assert the generating
% identities as axioms and build a congruence from them.




% \subsection{On the meaning of generation and the admissibility of structural
% rules}

% % Since, the derivable judgments of a type theory are, in a sense,
% % generated by the rules of that type theory it is easy enough then
% % to believe that, for any presentation 
% % \[
% % \xymatrix{\mathfrak{F}\mathcal{R}\ar@<.25pc>[r]\ar@<-.25pc>[r] & \mathfrak{F}\mathcal{G}}
% % \]
% %  of a PROP $\mathcal{C}$, the term model $\mathsf{TM}\left(\mathsf{PTT}_{\langle\mathcal{G}|\mathcal{R}\rangle}\right)$
% % is equivalent to $\mathcal{C}$.

% % Indeed, Shulman shows that:
% % \begin{itemize}
% % \item the term model of the type theory$\mathsf{PTT}_{\left\langle \mathcal{G}| \emptyset\right\rangle }$
% % enjoys the universal property of the free PROP on a signature (\textbf{Theorem
% % 5.17});
% % \item the derivable equality judgments of $\mathsf{PTT}_{\langle\mathcal{G}|\mathcal{R}\rangle}$
% % comprise a congruence $\sim_{R}$ on $\mathfrak{F}\mathcal{G}$ (\textbf{Proposition
% % 6.1}); and
% % \item the PROP $\mathfrak{F}G_{\sim_{R}}$ is equivalent to the PROP $\mathscr{C}$
% % presented 
% % \[
% % \xymatrix{\mathfrak{F}\mathcal{R}\ar@<.25pc>[r]\ar@<-.25pc>[r] & \mathfrak{F}\mathcal{G}}
% % \]
% %  (\textbf{Theorem 6.2}) 
% % \end{itemize}
% % Before one makes the jump from appreciating the naturality of the
% % work to thinking it obvious, we must acknowledge something we've intentionally
% % obscured: exactly how a signature $G$ generates the rules of the
% % typing judgment. The 'obvious' way to define the rules of the typing judgment such that
% % we could expect a result like Theorem 5.17 would be to specify:

% Let us now have a deeper look at exactly how a signature $G$ generates the rules of the typing judgment. The 'obvious' way would be to define a series of rule which would respectively allow us to:
% \begin{enumerate}
%     \item match the application of a morphism $f$ to a term $(M_{1},\dots,M_{n})$;
%     \item concatenate terms (i.e. effectively tensoring lists) to obtain terms of type $$\left(M_{1},\dots,M_{n},N_{1},\dots,N_{m}\right):\left(A_{1},\dots,A_{n},B_{1},\dots,B_{m}\right)$$ from two distinct terms in $A_i$ and $B_j$;
%     \item describe permutations inside the lists of terms, i.e. something that allows us to incorporate things like $\left(M_{\sigma\left(1\right)},\dots,M_{\sigma\left(n\right)}\right):\left(A_{\sigma\left(1\right)},\dots,A_{\sigma\left(n\right)}\right)$ in the type theory.
% \end{enumerate}


% % What does the typing judgment rules need to allow? 

% % Need a rule that matches the application of a morphism $f$ to a term $(M_{1},\dots,M_{n})$.

% % Need a rule that concatenates terms (i.e. effectively tensoring lists) to obtain terms of type $\left(M_{1},\dots,M_{n},N_{1},\dots,N_{m}\right):\left(A_{1},\dots,A_{n},B_{1},\dots,B_{m}\right)$ from two distinct terms in $A_i$ and $B_j$.

% % Need a rule to describe permutations inside the lists of terms, i.e. something that allows us to incorporate things like $\left(M_{\sigma\left(1\right)},\dots,M_{\sigma\left(n\right)}\right):\left(A_{\sigma\left(1\right)},\dots,A_{\sigma\left(n\right)}\right)$ in the type theory.

% % \begin{itemize}
% % \item a rule something like 
% % \[
% % \frac{\begin{gathered}\Gamma\vdash\left(M_{1},\dots,M_{n}\right):\left(A_{1},\dots,A_{n}\right)\\
% % f\in\mathcal{G}\left(A_{1},\dots,A_{n};B_{1},\dots,B_{m}\right)
% % \end{gathered}
% % }{\Gamma\vdash\left(f_{\left(1\right)}\left(M_{1},\dots,M_{n}\right),\dots,f_{\left(m\right)}\left(M_{1},\dots,M_{n}\right)\right):\left(B_{1},\dots,B_{m}\right)}
% % \]
% % which would allow us to 'apply' a morphism 
% % \[
% % f\in\mathcal{G}\left(A_{1},\dots,A_{n};B_{1},\dots,B_{m}\right)
% % \]
% %  to a term $\left(M_{1},\dots,M_{n}\right)$ of $\left(A_{1},\dots,A_{n}\right)$;
% % \item a rule something like 
% % \[
% % \frac{\Gamma\vdash\left(M_{1},\dots,M_{n}\right):\left(A_{1},\dots,A_{n}\right)\quad\Delta\vdash\left(N_{1},\dots N_{m}\right):\left(B_{1},\dots,B_{m}\right)}{\Gamma,\Delta\vdash\left(M_{1},\dots,M_{n},N_{1},\dots,N_{m}\right):\left(A_{1},\dots,A_{n},B_{1},\dots,B_{m}\right)}
% % \]
% % which would allow us to tensor two morphisms together; and
% % \item a rule something like
% % \[
% % \frac{\Gamma\vdash\left(M_{1},\dots,M_{n}\right):\left(A_{1},\dots,A_{n}\right)\quad\sigma\in S_{n}}{\Gamma\vdash\left(M_{\sigma\left(1\right)},\dots,M_{\sigma\left(n\right)}\right):\left(A_{\sigma\left(1\right)},\dots,A_{\sigma\left(n\right)}\right)}
% % \]
% % corresponding to the exchange isomorphisms permuting the generating
% % objects in a list thereof $\left(A_{1},\dots,A_{n}\right)$.
% % \[
% % \prftree{\Gamma\vdash M:A}{f\in\mathcal{G}\left(A;B_{1},B_{2}\right)}{B}
% % \]
% % \end{itemize}
% The problem with this 'obvious' way however is that derivations for typing
% judgments would be non-unique. For example, we see that with this logic, the two different associations of three composable morphisms $f:A\longrightarrow B$,
% $g:B\longrightarrow C$, and $h:C\longrightarrow D$ would yield distinct derivations of the same typing judgment, notably:
% \[
% \prftree{\prftree{x:A\vdash f\left(x\right):B}{y:B\vdash g\left(y\right):C}{x:A\vdash g\left(f\left(x\right)\right):C}}{z:C\vdash h\left(z\right):D}{x:A\vdash h\left(g\left(f\left(x\right)\right)\right)}
% \]
% and
% \[
% \prftree{x:A\vdash f\left(x\right):A}{\prftree{y:B\vdash g\left(y\right):C}{z:C\vdash h\left(z\right):D}{y:A\vdash h\left(g\left(y\right)\right):D}}{x:A\vdash h\left(g\left(f\left(x\right)\right)\right)}
% \]
% As induction over derivations is far more cumbersome than induction
% over derivable judgments Shulman opts for a more sophisticated tack by defining the rules for the typing judgments such that:
% \begin{itemize}
% \item derivations of typing judgments are unique; and
% \item the structural rules, i.e. the rules corresponding to composition,
% tensorings, and exchange are admissible which allow us to reason with them even if they are not the actual rules of the type theory. %{\color{red} We need to define `admissible' i.e. meaning that we can reason with them but do not introduce new derivations.}
% \end{itemize}
% %As such, not only are Theorem 5.17, Proposition 6.1, and Proposition 6.2 provable by way of a much tamer induction, but
% Any user of the
% type theory may invoke these more naive 'structural' rules in derivations
% and then freely ignore the multiplicity of derivations such reasoning
% may bring about. 

\section{Example: The Free Dual Pair}\label{ex:TheFreeDualPair}
%\newcommand{\ev}{\mathsf{ev}}
%\newcommand{\coev}{\mathsf{coev}}

% We have now covered all the theory and important concepts related to the construction of a type theory for an arbitrary symmetric monoidal category. The rest of this blog post will now focus on working out the details of a very simple example, namely the type theory associated to a dual pair in a symmetric monoidal category. This corresponds to the categorification of the bijection 
% \[
% \mathsf{Hom}\left(A\otimes V,B\right)\liso\mathsf{Hom}\left(A,V^{*}\otimes B\right)
% \]
% between a vector space $V$ and its dual vector space $V^{*}$, which is natural in vector spaces $A$ and $B$.

Having sketched the basics of Shulman's \textsf{PTT} and how a presentation for a \textsf{PROP} specifies the rules of \textsf{PTT} for that \textsf{PROP}, we may now attend to an important and illuminating example. We will develop the practical type theory of the free dual pair.

Recall that a dual pair in a symmetric monoidal category abstracts the relationship

\[
     \mathsf{Hom}\left(A\otimes V,B\right)\liso\mathsf{Hom}\left(A,V^{*}\otimes B\right)
\]

between a vector space $V$ and its dual, $V^*$.

\begin{defn}
A dual pair $\left(D,D^{*},\coev,\evmap\right)$ in a symmetric monoidal
category $\left(\mathfrak{C},\left(\_,\_\right),\left(\right)\right)$
is comprised of:
\begin{itemize}
\item a pair of objects $D$ and $D^{*}$ of $\mathfrak{C}$;
\item a morphism $\coev:\mathbf{1}\longrightarrow D\otimes D^{*}$; and
\item a morphism $\evmap:D^{*}\otimes D\longrightarrow\mathbf{1}$
\end{itemize}
satisfying the triangle identities:

\begin{align*}
    \vcenter{\vbox{\xymatrix{
        D\ar@{=}[dd]
        \ar[dr]^{\left(\coev,D\right)}
            \\
        %empty
            &
            \left(D,D^{*},D\right)
            \ar[dl]^{\left(D,\evmap\right)}
                \\
        D
    }}}
        &
        \mathrm{ \ \ \ \ \ \ \ \ \ \  \ and }
            &
            \vcenter{\vbox{\xymatrix{
                D^{*}
                \ar@{=}[dd]
                \ar[dr]^{\left(D^{*},\coev\right)}
                    \\
                %empty
                    &
                    \left(D^{*},D,D^{*}\right)
                    \ar[dl]^{\left(\evmap,D^{*}\right)}
                        \\
                D^{*}
    }}}
    \end{align*}
\end{defn}

These data suggest a presentation $(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$ for a \textsf{PROP}, in particular the \textbf{free dual pair}. We set:

\begin{itemize}
    \item $\mathbf{X}_0 = \Set{D,D^\star}$;
    \item $\mathbf{X}_1 = \Set{
        \coev:\left(\right) \longrightarrow \left(D,D^{*}\right), \
        \evmap:\left(D^{\star},D\right)\longrightarrow \left(\right)
    }$; and
    \item $\mathbf{R} =
    \Set{
        \mathsf{triangle}:(D,\evmap) \circ (\coev,D) = \id_{D}, \ 
        \mathsf{triangle}^{*}:(\evmap,D^*)\circ(D^*,\coev) = \id_{D^*}
    }$
\end{itemize}

% \[
% \mathcal{G}=\left(\left\{ D,D^{*}\right\} ,\left\{ \coev:\left(\right)\longrightarrow\left(D,D^{*}\right),\evmap:\left(D^{\star},D\right)\longrightarrow\left(\right)\right\} \right),
% \]
%  we set 
% \[
% \mathcal{R}=\left(\left\{ D,D^{*}\right\} ,\left\{ \mathsf{triangle}:D\longrightarrow D,\mathsf{triangle}^{*}:D^{*}\longrightarrow D^{*}\right\} \right),
% \]
% and for the maps defining the presentation we pick the ones generated
% by the assignments
% \[
% \xymatrixrowsep{0pc}
% \xymatrix{\mathsf{triangle}\ar@{|->}[r] & \id_{D}\\
% \mathsf{triangle^{*}}\ar@{|->}[r] & \id_{D^{*}}
% }
% \]
% and
% \[
% \xymatrixrowsep{0pc}\xymatrix{\mathsf{triangle}\ar@{|->}[r] & \left(D,\evmap\right)\circ\left(\coev,D\right)\\
% \mathsf{triangle^{*}}\ar@{|->}[r] & \left(\evmap,D^{*}\right)\circ\left(D^{*}\coev\right)
% }
% \]

\subsection{The type theory of the free dual pair}
We will now develop the rules of the type theory for the free dual pair from the data this presentation $(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$. While we have not bothered with them until now, Shulman's practical type theory does include rules for term formation. In the case of the practical type theory for the free dual pair, the rules for the term judgment are few. We present a streamlined version of them:
%
\begin{align*}
\vcenter{\vbox{\inferrule{\left(x:A\right)\in\Gamma}{\Gamma\vdash x\ \mathsf{term}}}}
&&
\vcenter{\vbox{\inferrule{1\leq k\leq2}{\coev_{\left(k\right)} \ \mathsf{term}}
}}
&&
\vcenter{\vbox{\prftree{\Gamma\vdash m\ \mathsf{term}}{\Gamma\vdash n\ \mathsf{term}}{\Gamma\vdash\evmap\left(m,n\right)\ \mathsf{term}}}}
\end{align*}
The first rule is the usual variable rule which gives us the terms in which we may derive the typing judgments corresponding to identities. The second one gives us terms in which we may derive co-evaluation as a typing judgment. Finally, the last one gives us the terms in which we may derive evaluation as a typing judgment.
%
%\begin{itemize}
%\item the rule $$\vcenter{\vbox{\inferrule{\left(x:A\right)\in\Gamma}{\Gamma\vdash x\ \mathsf{term}}}}$$ is the usual variable rule giving us the terms in which we'll be able to derive the typing judgments corresponding to identities;
%\item the rule $$\vcenter{\vbox{\inferrule{1\leq k\leq2}{\coev_{\left(k\right)} \ \mathsf{term}}
%}}$$
%which gives us terms in which we'll be able to derive co-evaluation as a typing judgment; and
%\item the rule $$\vcenter{\vbox{\prftree{\Gamma\vdash m\ \mathsf{term}}{\Gamma\vdash n\ \mathsf{term}}{\Gamma\vdash\evmap\left(m,n\right)\ \mathsf{term}}}}$$ gives us the terms with which we'll be able to derive evaluation as a typing judgment.
%\end{itemize}
%

For the typing judgments, we have two (again slightly streamlined) rules:
\begin{itemize}
    \item the so-called \textbf{generator rule}
        \[
            \inferrule{
                \Gamma
                    \in
                    \left(
                        %\overrightarrow{m},
                        %\dots,
                        %\overrightarrow{n},
                        \overrightarrow{p},
                        \dots,
                        \overrightarrow{q},
                        \overrightarrow{r}
                        |
                        \overrightarrow{z}
                    \right)
                    :
                    \left(
                        %\overrightarrow{A},
                        %\dots,
                        %\overrightarrow{B},
                        \overrightarrow{C},
                        \dots,
                        \overrightarrow{D},
                        \overrightarrow{E}
                    \right)
                    \\\\
                %f:\overrightarrow{A} \rightarrow \overrightarrow{F} \in \mathbf{X}_1,
                %    \\
                %    \dots
                %        \\
                %        g:\overrightarrow{B} \rightarrow \overrightarrow{G} \in \mathbf{X}_1
                %            \\\\
                h:\overrightarrow{C} \rightarrow () \in \mathbf{X}_1
                    \\
                    \dots
                        \\
                        k:\overrightarrow{D} \rightarrow () \in \mathbf{X}_1
                            \\\\
                \sigma : \left(
                            \overrightarrow{F},
                            \dots,
                            \overrightarrow{G},
                            \overrightarrow{E}
                         \right) \overset{\sim}{\longrightarrow} \bigtriangleup
                         \in \Sigma_{\mathbf{X}_0}
                            \\
                            \tau \in \mathsf{Shuffle}\left(
                                                        h,\dots,k; \overrightarrow{z}
                                                     \right)
            }{
                \Gamma \vdash \left(
                                \sigma
                                \left(
                                    \overrightarrow{f}(\overrightarrow{m}),
                                    \dots,
                                    \overrightarrow{g}(\overrightarrow{n}),
                                    \overrightarrow{r}
                                \right)
                                \middle|
                                \tau
                                \left(
                                    h(\overrightarrow{p}),
                                    \dots,
                                    k(\overrightarrow{p}),
                                    \overrightarrow{z}
                                \right)
                              \right)
            }
        \]
        corresponds to applying a tensor product followed by a braiding $\sigma$ and a shuffling of scalars. The tensor product is taken between generating scalar-valued functions $h,\dots,k$ (which can only be some number of copies of $\evmap$ in our case) and the identity on some object, here $\overrightarrow{E}$. And,
 %       
 %       
%        of:
%        \begin{itemize}
%            \item generating scalar-valued functions  $h,\dots,k$ , which can only be some number of copies of $\evmap$ in our case; and
%            \item the identity on some object, here $\overrightarrow{E}$
%        \end{itemize}
%        followed by:
%        \begin{itemize}
%            \item a braiding $\sigma$; and
%            \item shuffling of scalars (in a symmetric strict monoidal category all scalars commute on the nose)
%        \end{itemize} and
        \item the so-called \textbf{identity rule}
            \[
            \inferrule{
                f:() \rightarrow \overrightarrow{B} \in \mathbf{X}_1
                    \\
                    \dots
                        \\
                        g:() \rightarrow \overrightarrow{C} \in \mathbf{X}_1
                            \\\\
                % h:() \rightarrow ()
                %     \\
                %     \dots
                %         \\
                %         k:() \rightarrow ()
                %             \\\\
                \sigma:\left(
                    \overrightarrow{A},
                    \overrightarrow{B},
                    \dots,
                    \overrightarrow{C}
                    \right) \overset{\sim}{\longrightarrow} \bigtriangleup \in \Sigma_{\mathbf{X}_0}
            }{
                \overrightarrow{x}:\overrightarrow{A} \dashv \left(
                                                                \sigma \left(
                                                                    \overrightarrow{x},
                                                                    \overrightarrow{f},
                                                                    \dots,
                                                                    \overrightarrow{g}
                                                                \right)
                                                                \middle|
                                                                h,\dots,k
                                                             \right):\bigtriangleup
            }
            \]
            which corresponds to applying a braiding $\sigma$ to the tensoring of some number of generating constants, here $f,\dots,g$ (which can only be some number of copies of $\coev$), and the identity on some object $\overrightarrow{A}$.
%            \begin{itemize}
%                \item applying a braiding $\sigma$
%            \end{itemize}
%            to the tensoring of:
%            \begin{itemize}
%                \item some number of generating constants, here $f,\dots,g$, which can only be some number of copies of $\coev$; and
%                \item the identity on some object $\overrightarrow{A}$
%            \end{itemize}
\end{itemize}

\begin{remark} Here we are ignoring the notion consideration of ``activeness'', a technical device introduced to rigidify the type theory into one with unique derivations of judgments by providing a canonical form for 1-cells. We also ignored the syntactic sugar of labels, which act like formal variables for the unit type.
\end{remark}
%
%
Lastly, for the equality judgment we have axioms
%
 %
        \[
            \inferrule{\msf{triangle}: (\id, \coev) \circ (\evmap, \id) = \id_{D}
                            \in
                                \mathbf{R}
                        }{
                            m:D \vdash \left(\coev_{\left(1\right)}|\evmap\left(\coev_{\left(2\right)},M\right)\right) = m:D
                        }
        \]
        and    
        \[
            \inferrule{
                            \mathsf{triangle}^{*}:(\evmap,D^\star)\circ(D^\star,\coev) = \id_{D^\star} \in \mathbf{R}
                        }{
                            n:D^{*}\vdash\left(\coev_{\left(2\right)} \middle| \evmap\left(N,\coev_{\left(1\right)}\right)\right)=n:D^{*}
                        }
        \]
    together with enough rules  so that $=$ acts as a congruence relative to all of the other rules.

\begin{example} Consider the composition
\[
    (D)\xrightarrow{(\coev,D)} (D,D^{*},D) \xrightarrow{(D,\evmap)} (D)
\]
%
%
%\[
%\xymatrixcolsep{4pc}\xymatrix{\left(D\right)\ar[r]^{\left(\coev,D\right)} & \left(D,D^{*},D\right)\ar[r]^{\left(D,\evmap\right)} & \left(D\right)}
%\]
% and 
% \[
% \xymatrixcolsep{4pc}\xymatrix{\left(D^{*}\right)\ar[r]^{\left(D^{*},\coev\right)} & \left(D,D^{*},D\right)\ar[r]^{\left(D,\evmap\right)} & \left(D\right)}
% \]
%
%
which  corresponds to the typing judgement
%
\[
    x:D\vdash\left(\coev_{\left(1\right)}|\evmap\left(\coev_{\left(2\right)},x\right)\right)
\]
%
This typing judgement admits the following derivation
%
\[
\inferrule*{
    \inferrule*{
        \coev:() \rightarrow (D,D^*) \in \mathbf{X}_1
            \\
            \left(132\right):\left(D,D,D^{*}\right)\liso\left(D,D^{*},D\right)
    }{
        x:D\vdash\left(\coev_{\left(1\right)},\coev_{\left(2\right)},x\right):D
    }
        \\
        \evmap: (D^*,D) \rightarrow () \in \mathbf{X}_1
    }{
        x:D\vdash\left(\coev_{\left(1\right)}|\evmap\left(\coev_{\left(2\right)},x\right)\right)
    }
\]
where:
\begin{itemize}
    \item the first rule is an instance of the identity rule with premised generators $\coev$ and the braiding $(132)$; and
    \item the second rule is an instance of the identity rule with the typing judgement $$x:D\vdash\left(\coev_{\left(1\right)},\coev_{\left(2\right)},x\right):D$$ the consequent of the first rule and the additional hypothesis being the generator \textsf{ev}.  
\end{itemize} 
\end{example}
%




\subsection{"Elements" of dual objects}
We have now developed a type theory for the free dual pair which endows
the dual objects $D$ and $D^{*}$ with a universal notion of element (that of $D$-typed term and $D^*$-typed term respectively).
Since the notion of dual pair abstracted the instance of a pair of
dual vector spaces, which in particular have actual elements, it behooves
us to ask:
\begin{quotation}
``to what extent is term of type $D$ like a vector (in $D$)?''
\end{quotation}
The answer is both practical and electrifying (though perhaps the
authors of this post are too easily electrified).

It's easy enough to believe that the evaluation map 
\[
\evmap:\left(D,D^{*}\right)\longrightarrow\left(\right)
\]
 endows the terms of type $D$, or $D^{*}$ for that matter, with a
structure of scalar valued functions on the other. The triangle identities impose the unique determination of terms of type $D$ or $D^*$ in terms of their values as given by $\evmap$.  Indeed consider that, for a finite dimensional vector space $V$ over a field
$k$, a basis $\left\{ \mathbf{e}_{i}\right\} _{i=1}^{n}$ for $V$
and a dual basis $\left\{ \mathbf{e}_{i}^{*}\right\} _{i=1}^{n}$
for $V^{*}$ give us an elegant way to write $\coev$ and the
first triangle identity. We write
\[
\xymatrixrowsep{0pc}\xymatrix{k\ar[r]^{\coev} & V\otimes V^{*}\\
x\ar@{|->}[r] & \sum_{i=1}^{n}\mathbf{e}_{i}\otimes\mathbf{e}_{i}^{*}
}
\]
and see that

\begin{align*}
    \vcenter{\vbox{\xymatrix{
        V
        \ar@{=}[dd]
        \ar[dr]^{\coev\otimes V}
            \\
        %empty
            &
            V\otimes V^{*}\otimes V
            \ar[dl]^{V\otimes\evmap}
                \\
        V
    }}}
        &
        \vcenter{\vbox{\xymatrix{
            \mathbf{v}
            \ar@{|->}[dd]
            \ar@{|->}[dr]
                \\
            %empty
                &
                \left(\sum_{i=1}^{n}\mathbf{e}_{i}\otimes\mathbf{e}_{i}^{*}\right)\otimes\mathbf{v}
                \ar@{|->}[dl]
                    \\
            \mathbf{v}=\sum_{i=1}^{n}\mathbf{e}_{i}^{*}\left(\mathbf{v}\right)\cdot\mathbf{e}_{i}
    }}}
\end{align*}
%
The observation for dual vector spaces
\[
    V \mathrm{ and } V^*=\mathsf{Hom}_{\mathsf{Vect}_k}\left(V,k \right)
\]
that the triangle identities hold is just the observation that a vector is precisely determined by its values: every vector $\mathbf{v}$  is equal to the un-named vector
\[
\sum_{i=1}^{n}\mathbf{e}_i^*\left( \mathbf{v}\right)\cdot \mathbf{e}_i
\]
which is defined by taking the values $\mathbf{e}^*_{i}\left( \mathbf{v} \right)$ at the dual vectors $\mathbf{e}_i^*$.
As part of the definition of a dual pair in an arbitrary symmetric strict monoidal category then, the triangle identities imposes this as a relationship between $\evmap$ and $\coev$. But within type theory, this sort of relationship between an un-named function and its values is familiar, indeed it is something very much like $\beta$-reduction.
%
 To see this more clearly, let us make a pair of notational changes. In place of writing 
\[
\left(x,y\right):\left(D^{*},D\right)\vdash\evmap\left(x,y\right):\left(\right)
\]
we will denote $\evmap$ infix by $\_\triangleleft\_$ and write
\[
\left(x,y\right):\left(D^{*},D\right)\vdash x\triangleleft y:\left(\right).
\]
Similarly, in place of writing 
\[
\vdash\left(\coev_{\left(1\right)},\coev_{\left(2\right)}\right):\left(D,D^{*}\right)
\]
 we will denote $\coev$ by the pair $\left(u,\lambda^{D}u\right)$
and write
\[
\vdash\left(u,\lambda^{D}u\right):\left(D,D^{*}\right).
\]
With this choice of notation then, the equality judgment which corresponds to
the first triangle identity is 
\[
x:D\vdash\left( u \; |\; \lambda^{D}u\triangleleft x\right)=x:D.
\]
%
Then, since $=$ is a congruence with respect
to substitution (recall that we promised that the rules for the equality judgement were precisely those  required for generating a congruence from a set of primitive relations), if we have, for some term $m$, the term $\lambda^{D}u\triangleleft m$
appearing in the scalars of a list of terms, then we may replace all
instances of $u$ in the rest of the term with $m$. While a mouthful,
this is a sort of "$\beta$-reduction for duality" allowing us to treat $\coev$ as a sort of $\lambda$-abstraction, as we suggested by the change in notation. Conceptually interesting in its own right, this observation also yields a one line
proof for a familiar theorem, namely the cyclicity of the trace.

\begin{example}
Consider two dual pairs 
\begin{align*}
\left(A,A^{*},\left(u,\lambda^{A}u\right),\_\triangleleft\_\right)
&&
\left(B,B^{*},\left(v,\lambda^{B}v\right),\_\triangleleft\_\right)
\end{align*}
in a symmetric strict monoidal category $\left(\mathfrak{C},\left(\_,\_\right),\left(\right)\right)$
and a pair of maps $f:A\longrightarrow B$
 and $g:B \longrightarrow A$. The trace $\mathsf{tr}\left(f\circ g\right)$ is defined as the composition 
\[
\xymatrixrowsep{0pc}\xymatrixcolsep{3pc}\xymatrix{\left(\right)\ar[r]^{\left(v,\lambda^{B}v\right)} & \left(B,B^{*}\right)\ar[r]^{f\circ g} & \left(B,B^{*}\right)\ar[r]^{\left(12\right)} & \left(B^{*},B\right)\ar[r]^{\_\triangleleft\_} & \left(\right)}
\]
where $(12)$ denotes the permutation of entries of the list. Likewise the trace $\mathsf{tr}\left(g\circ f\right)$ is the composition.
\[
\xymatrixrowsep{0pc}\xymatrixcolsep{3pc}\xymatrix{\left(\right)\ar[r]^{\left(u,\lambda^{A}u\right)} & \left(A,A^{*}\right)\ar[r]^{g\circ f} & \left(A,A^{*}\right)\ar[r]^{\left(12\right)} & \left(A^{*},A\right)\ar[r]^{\_\triangleleft\_} & \left(\right)}
.
\]
Using the notation introduced above it follows that $\mathsf{tr}\left(f\circ g\right)=\mathsf{tr}\left(g\circ f\right)$ as:
\begin{eqnarray*}
\mathsf{tr}\left(f\circ g\right) & \overset{\mathsf{def}}{=} & \left(\left|\lambda_{u}^{B}\triangleleft f\left(g\left(u\right)\right)\right.\right)\\
 & = & \left(\left|\lambda_{u}^{B}\triangleleft f\left(v\right)\right.,\lambda_{v}^{A}\triangleleft g\left(u\right)\right)\\
 & = & \left(\left|\lambda_{v}^{A}\triangleleft g\left(f\left(v\right)\right)\right.\right)\\
 & \overset{\mathsf{def}}{=} & \mathsf{tr}\left(g\circ f\right)
\end{eqnarray*}
Where the judged equalities are applications of "$\beta$-reduction
for a duality".
\end{example}

%\begin{lem}
%[Cyclicity of trace] Let $\left(\mathfrak{C},\left(\_,\_\right),\left(\right)\right)$
%be a symmetric strict monoidal category. Further let 
%\[
%\left(A,A^{*},\left(u,\lambda^{A}u\right),\_\triangleleft\_\right)
%\]
% and 
%\[
%\left(B,B^{*},\left(v,\lambda^{B}v\right),\_\triangleleft\_\right)
%\]
% be dual pairs in $\mathfrak{C}$, and $f:A\longrightarrow B$ and $g:B\longrightarrow A$
%be morphisms in $\mathfrak{C}$. Let $\mathsf{tr}\left(f\circ g\right)$ be
%the composition 
%\[
%\xymatrixrowsep{0pc}\xymatrixcolsep{3pc}\xymatrix{\left(\right)\ar[r]^{\left(v,\lambda^{B}v\right)} & \left(B,B^{*}\right)\ar[r]^{f\circ g} & \left(B,B^{*}\right)\ar[r]^{\left(12\right)} & \left(B^{*},B\right)\ar[r]^{\_\triangleleft\_} & \left(\right)}
%\]
%and likewise let $\mathsf{tr}\left(g\circ f\right)$ be the composition.
%\[
%\xymatrixrowsep{0pc}\xymatrixcolsep{3pc}\xymatrix{\left(\right)\ar[r]^{\left(u,\lambda^{A}u\right)} & \left(A,A^{*}\right)\ar[r]^{g\circ f} & \left(A,A^{*}\right)\ar[r]^{\left(12\right)} & \left(A^{*},A\right)\ar[r]^{\_\triangleleft\_} & \left(\right)}
%.
%\]
%Then, $\mathsf{tr}\left(f\circ g\right)=\mathsf{tr}\left(g\circ f\right)$.
%\end{lem}
%
%\begin{proof}
%\begin{eqnarray*}
%\mathsf{tr}\left(f\circ g\right) & \overset{\mathsf{def}}{=} & \left(\left|\lambda_{u}^{B}\triangleleft f\left(g\left(u\right)\right)\right.\right)\\
% & = & \left(\left|\lambda_{u}^{B}\triangleleft f\left(v\right)\right.,\lambda_{v}^{A}\triangleleft g\left(u\right)\right)\\
% & = & \left(\left|\lambda_{v}^{A}\triangleleft g\left(f\left(v\right)\right)\right.\right)\\
% & \overset{\mathsf{def}}{=} & \mathsf{tr}\left(g\circ f\right)
%\end{eqnarray*}
%Where the judged equalities are application of "$\beta$-reduction
%for a duality".
%\end{proof}


\end{document}
