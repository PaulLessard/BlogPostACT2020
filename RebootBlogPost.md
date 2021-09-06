# Shulman's Practical Type Theory for Symmetric Monoidal Categories

*guest post by [Nuiok Dicaire](https://www.inf.ed.ac.uk/people/students/Nuiok_Dicaire.html) and [Paul Lessard](https://sites.google.com/view/paul-roy-lessard/)*

Many well-known type theories, Martin-Löf dependent type theory or linear type theory for example, were developed as syntactic treatments of particular forms of reasoning. Constructive mathematical reasoning in the case of Martin-Löf type theory and resource dependent computation in the case of linear type theory. It is after the fact that these type theories provide convenient means to reason about locally Cartesian closed categories or $\star$-autonomous ones. In this post, a long overdue part of the Applied Category Theory Adjoint School (2020!?), we will discuss a then recent paper by Mike Shulman, 
*A Practical Type Theory for Symmetric Monoidal Categories*, where the author reverses this approach. 
Shulman starts with symmetric monoidal categories as the intended semantics and then (reverse)-engineers a syntax in which it is *practical* to reason about such categories.

Which properties of a type theory (for symmetric monoidal categories) make it practical? Shulman, synthesizing various observations, settles on a few basic tenets to guide the invention of the syntax and its interpretation into symmetric monoidal categories. We reduce these further to the conditions that the type theory be: (1) intuitive, (2) concise, and (3) complete.

<strong> Intuitive. </strong> 
First, a practical type theory should permit us to leverage our intuition for reasoning about "sets with elements". What this means in practice is that we require a "natural deduction style" type theory, in which contexts look and feel like choosing elements, and typing judgements look and feel like functions of sets. Moreover, we also require an internal-language/term-model relationship with symmetric monoidal categories which provide correspondences:
\[
\array{ \arrayopts{ \frame{none} 
                    \rowalign{bottom} 
                    \rowlines{none}
                  }                    
        \mathbf{Category} \quad & & \quad \mathbf{Type} \;\mathbf{Theory} \\
        \mathrm{objects}  \quad & \leftrightarrow & \quad \mathrm{contexts} \\
        \mathrm{morphisms}  \quad & \leftrightarrow & \quad \mathrm{typing} \; \mathrm{judgments} \\
        \mathrm{commuting}\;\mathrm{diagrams} \quad & \leftrightarrow & \quad \mathrm{equality} \; \mathrm{judgments}
}
\]

<strong> Concise. </strong> 
When stripped of the philosophical premises of what terms, types, judgements etc. <em> are </em>>, the rules of a type theory can be seen to generate its derivable judgments. It is therefore desirable that the translation between symmetric monoidal categories and the rules of their associated type theories proceed by way of the most concise combinatorial description of symmetric monoidal categories possible.

<strong> Complete. </strong> 
Lastly we ask that, given a presentation for a symmetric monoidal category, the type theory we get therefrom should be complete. By this, we mean that a proposition should hold in a particular symmetric monoidal category if and only if it is derivable as a judgment in the associated type theory.


## Symmetric Monoidal Categories and Presentations of $\mathsf{PROP}$s

While it is well-known that every symmetric monoidal category is equivalent to a symmetric <i> strict </i> monoidal category, it is probably less well-known that every symmetric strict monoidal category is equivalent to a $\mathsf{PROP}$.

<strong> Definition. </strong> A $\mathsf{PROP}$, $\mathfrak{P}=\left(\mathfrak{P},\mathbf{P}\right)$, consists of a set $\mathbf{P}$ of generating objects and a symmetric strict monoidal category $\mathfrak{P}$ whose underlying monoid of objects is the free monoid on the set $\mathbf{P}$.

This is not however too hard to see: the equivalence between $\mathsf{PROP}$s and symmetric monoidal categories simply replaces every equality of objects $A\otimes B = C$ with an isomorphism $A \otimes B \overset{\sim}{\longrightarrow} C$, thereby rendering the monoidal product to be free. We will develop what we mean by presentation over the course of a few examples. In doing so we hope to give the reader a better sense for $\mathsf{PROP}$s.

<strong> Example. </strong>
Given a set $\mathbf{X}$, let $\Sigma_{\mathbf{X}}$ be the <strong>free permutative category on</strong> $\mathbf{X}$. This is a symmetric monoidal category whose monoid of objects is the monoid of lists drawn from the set $\mathbf{X}$ and whose morphisms are given by the expression
\[
    \Sigma_{\mathbf{X}}\left(\overrightarrow{X},\overrightarrow{Y}\right)
    =
    \left\{ \sigma \in S_{n} \Big| \overrightarrow{X_\sigma}=\overrightarrow{Y} \right\}
\]
(where by $\overrightarrow{X_\sigma}$ we mean the reorganization of the list $\overrightarrow{X}$ according to the permutation $\sigma$). For every set $\mathbf{X}$, $\Sigma_{\mathbf{X}}$ is a $\mathsf{PROP}$.

<strong> Example. </strong> For a more complicated example, let $\mathbf{X}_0$ be a set and let
\[
    \mathbf{X}_1
    =
    \left\{
      (f_i,\overrightarrow{X}_i,\overrightarrow{Y}_i)
      \right\}_{i\in I}
\]
be a set of triples comprised of names $f_i$ and pairs of lists $\left(\overrightarrow{X}_i,\overrightarrow{Y}_i\right)$ valued in $\mathbf{X}_0$. Let $F\left(\mathbf{X}_1,\mathbf{X}_0\right)$ denote the free symmetric monoidal category generated by $\Sigma_{\mathbf{X}_0}$ together with additional arrows $f_{i}:\overrightarrow{X}_i \longrightarrow \overrightarrow{Y}_i$ for each $i\in I$. Then $F\left(\mathbf{X}_1,\mathbf{X}_0\right)$ is also a $\mathsf{PROP}$.

Importantly, this second example is very nearly general - every $\mathsf{PROP}$ admits a bijective-on-objects and full, but not in general faithful, functor from some $\mathsf{PROP}$ of the form $F\left(\mathbf{X}_1,\mathbf{X}_0\right)$.

<strong> Example. </strong>
 Let  $\mathbf{X}_0$ and $\mathbf{X}_1$ be as in the previous example and let
 \[
    \mathbf{R}=\Big\{ (s_j,t_j) \in \mathsf{Mor}\big(F\left(\mathbf{X}_1,\mathbf{X}_0\right)\big)^2 \Big| j \in J \Big\}
 \]
 be a set of pairs of morphisms in the $\mathsf{PROP}$ $F\left(\mathbf{X}_1,\mathbf{X}_0\right)$. Let $F\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)$ be the quotient of the symmetric monoidal category $F\left(\mathbf{X}_1,\mathbf{X}_0\right)$ by the congruence generated by $R \subset \mathsf{Mor}\big(F(\mathbf{X}_1,\mathbf{X}_0)\big) \times \mathsf{Mor}\big(F\left(\mathbf{X}_1,\mathbf{X}_0\right)\big)$.

This last example is fully general. Every $\mathsf{PROP}$, hence every symmetric monoidal category, is equivalent to a $\mathsf{PROP}$ of the form $F\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)$.

<strong> Remark. </strong> If (generalized) computads are familiar, you may notice that our three examples here are free $\mathsf{PROP}$s on $0$, $1$, and $2$-computads.


## From Presentations to Type Theories

It is from these presentations $\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)$ of $\mathsf{PROP}$s that we will build type theories $\mathsf{PTT}_{\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)}$ for the symmetric monoidal categories $F\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)$. Indeed, reading $\rightsquigarrow$ as ``gives rise to'', we will see:
\[
\array{ \arrayopts{ \frame{none} 
                    \rowalign{bottom} 
                    \rowlines{none}
                  }                    
        \mathbf{Generators} \quad & & \quad \mathbf{Judgements} \\
        \mathbf{X}_0 \quad & \rightsquigarrow & \quad \mathrm{contexts} \\
        \mathbf{X}_1 \quad & \rightsquigarrow & \quad \mathrm{typing} \; \mathrm{judgments} \\
        \mathbf{R} \quad & \rightsquigarrow & \quad \mathrm{equality} \; \mathrm{judgment}
}
\]

### Contexts

The contexts (usually denoted $\Gamma,\;\Delta$, etc.) of the type theory $\mathsf{PTT}_{(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)}$  are lists
    \[
        x_{1}:A_{1},\dots,x_{n}:A_{n}
    \]
of typed variables, where the $A_i$ are elements of the set $\mathbf{X}_{0}$. It's not hard to see that, up to the names of variables, contexts are in bijection with $\mathsf{List}\left(\mathbf{X}_0\right)$.

### Typing Judgments

As promised, typing judgments correspond to morphisms in $F\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)$. Here are some examples of morphisms and their corresponding judgements:
\[
\array{ \arrayopts{ \frame{none} 
                    \rowalign{bottom} 
                    \rowlines{none}
                    \colalign{right left}
                  }                    
        \mathbf{Morphisms} \quad & & \quad \mathbf{Typing} \;\mathbf{Judgements} \\
        f:(A) \rightarrow (B)  \quad & \leftrightarrow & \quad x:A\vdash f(x):B \\
        h:(A)\rightarrow (B_{1},B_{2})  \quad & \leftrightarrow & \quad x:A\vdash\left(h_{(1)}(x),h_{(2)}(x)\right):B \\
        z:() \rightarrow () \quad & \leftrightarrow & \quad \vdash \left(|z^{a}\right):()
}
\]
The rules from which these judgments may be derived correspond, roughly speaking, to applying a tensor product of generating morphisms in $\mathbf{X}_1$ composed with a braiding - something along the lines of:
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{none solid}
                    \colalign{center}
                  } 
\Gamma \dashv \left( \overrightarrow{m}, \dots ,\overrightarrow{n} | \overrightarrow{z}\right) : \left( \overrightarrow{A}, \dots, \overrightarrow{B}\right) \\

    \left(f:\overrightarrow{A} \rightarrow \overrightarrow{F}\right) \in \mathbf{X}_1 
    \cdots \; 
    \left(g:\overrightarrow{B} \rightarrow \overrightarrow{G}\right) \in \mathbf{X}_1 
\quad
    \left( \sigma : \left(\overrightarrow{F},\dots, \overrightarrow{G}\right) \rightarrow \bigtriangleup \right) \in \Sigma_{\mathbf{X}_0} \\
 
    \Gamma \dashv \left( \sigma \left( \overrightarrow{f}\left(\overrightarrow{m}\right),\dots,\overrightarrow{g}\left( \overrightarrow{n}\right) \right) \right) : \bigtriangleup
}
\]
in which:
<ul>
  <li> $\Gamma$ is a context, and $\Delta$ is a (list of) type(s);
</li>
  <li> $\overrightarrow{m}, \dots ,\overrightarrow{n}$ are terms of types $\overrightarrow{A}, \dots , \overrightarrow{B}$ respectively;
</li>
  <li> the $f$ through $g$ are generating arrows in the set $\mathbf{X}_1$; and
</li>
  <li> $\sigma$ is the avatar in $\Sigma_{\mathbf{X}_0}$ of some permutation.
</li>
</ul>
Now, it is rather clear that we are hiding something - the gory details of the rules from which the typing judgments are derived (the so-called identity and generator rules in Shulman's paper). However, the reader should rest assured that not only are the details not that onerous, but the more naive structural rules corresponding to tensoring, composition, and braiding are admissible. In practical terms, this means that one is simply free to work with these more intuitive rules.


### Equality Judgments

Equality judgments, for example something of the form $x:A\vdash h (x)=f\big(g(x)\big):C,$ which in categorical terms corresponds to a commuting diagram

<img width = "150" src = "http://math.ucr.edu/home/baez/mathematical/ACT2020/Lessard/equality_judgement_diag.png" alt = ""/>

<!-- <img width = "150" src="https://drive.google.com/file/d/1DGFUbSEHRpxj3PwTh82yJ88ZKGPiPPQU/view?usp=sharing" alt = ""/>
-->

are similarly derived from rules coming from the set $\mathbf{R}$. We will be more explicit later on within the context of an example.



## How do Symmetric Monoidal Categories fit into all this?

Until this point it is not actually terribly clear what makes this type theory specifically adapted to symmetric monoidal categories as opposed to Cartesian monoidal categories. After all, we have written contexts as lists precisely as we would write contexts in a Cartesian type theory. 

Although we may not always think about it, we write contexts in Cartesian type theories as lists of typed variables because of the universal property of the product - a universal property characterized in terms of projection maps. Indeed, in a Cartesian type theory, a list of typed terms can be recovered from the list of their projections. This is not the case for arbitrary symmetric monoidal products; in general there are no projection maps. And, even when there are maps with the correct domain and codomain, there is no guarantee that they have a similar computation rule (the type theoretic avatar of a universal property).

To illustrate this in a mathematical context, consider a pair of vector spaces $U_1$ and $U_2$. Any element $z\in U_1 \times U_2$ of the Cartesian product of $U_1$ and $U_2$ is uniquely specified by the pair of elements $\mathsf{pr}_{1}(z) \in U_1$ and $\mathsf{pr}_{2}(z)\in U_2$ - $z=\left(\mathsf{pr}_1(z),\mathsf{pr}_2(z)\right)$. However, elements of the tensor product $U_1 \otimes U_2$ need not be simple tensors of the form $x \otimes y$ and instead are generally linear combinations $\sum_{i=1}^{k}x_{1,i} \otimes x_{2,i}$ of simple tensors.

Provided we are careful however - meaning we do not perform any "illegal moves" in a sense we will make clear - we can still use lists. This is what Shulman does in adapting Sweedler's notation. Consider a general element
    \[
        \sum_{i=1}^{k}x_{1,i}\otimes x_{2,i} \in U_1 \otimes U_2
    \]
In Sweedler's notation this is written as $\left(x_{(1)}, x_{(2)}\right)$ with the summation, indices, and tensor symbols all dropped. Provided we make sure that any expression in which $(x,y)$ appears is linear in both variables, this seeming recklessness introduces no errors.

To see how this plays out, suppose that we have a morphism $f$ with domain $A$ and co-domain being the tensor product $\left(B_1,...,B_n\right)$. In Shulman's adaptation of Sweedler's notation this corresponds to the judgment:
\[
a:A \vdash 
\left(
  f_{\left(1\right)}
  \left(
    a
  \right),
  \dots,f_{\left(n\right)}
  \left(
    a
  \right)
\right)
:
\left(
  B_{1},\dots,B_{n}
\right)
\]


Importantly, our typing rules will never derive the judgment $a:A\dashv f_{(k)}:B_k$ and we will only be able to derive $a:A \dashv \mathsf{pr}_k \left(f_{\left(1\right)}\left(a\right),\dots,f_{\left(n\right)}\left(a\right)\right):B_k$ if we have $\mathsf{pr}_k:\left(B_1,\dots,B_n\right) \rightarrow B_k$ in $\mathbf{X}_1$ and more, unless $\mathbf{R}$ specifies that $\mathsf{pr}_k$ acts like a projection, $\mathsf{pr}$ is but a name.

Since this type theory allows us to pretend, in a sense, that types are ``sets with elements'', the symmetric monoidal aspect of the type theory can be moralized as:
<ul>
  <li> terms of product types are not-necessarily-decomposable tuples;
</li>
</ul>
whereas in a Cartesian ``sets with elements'' style type theory:
<ul>
  <li> terms of product types are decomposable tuples.
</li>
</ul>

<strong> Remark. </strong>
Taking a hint from the bicategorical playbook can give us a more geometric picture of the difference between an indecomposable tuple and a decomposable one. Since every symmetric monoidal category is also a bicategory with a single object, a typed term, usually a $1$-cell, also corresponds to $2$-cells between (directed) loops. In this vein we may think of an indecomposable tuple $\left(x_{(1)},x_{(2)},\dots,x_{(n)}\right):\overrightarrow{A}$ as an $n$-sphere in $\overrightarrow{A}$ whereas a decomposable one, say $(x,y,\dots,z):\overrightarrow{A}$, corresponds to a torus (of some dimension) in  $\overrightarrow{A}$.


## Example: The Free Dual Pair

Having sketched the basics of Shulman's $\mathsf{PTT}$ and how a presentation for a $\mathsf{PROP}$ specifies the rules of $\mathsf{PTT}$ for that $\mathsf{PROP}$, we may now attend to an important and illuminating example. We will develop the practical type theory of the free dual pair.

Recall that a dual pair in a symmetric monoidal category abstracts the relationship
\[
     \mathsf{Hom}(A\otimes V,B)\overset{\sim}{\longrightarrow} \mathsf{Hom}(A,V^{\star}\otimes B)
\]
between a vector space $V$ and its dual, $V^{\star}$.

<strong> Definition. </strong>
A dual pair $(D,D^{\star},\mathsf{coev},\mathsf{ev})$ in a symmetric monoidal
category $\big(\mathfrak{C},(- ,-),()\big)$
is comprised of:
<ul>
  <li> a pair of objects $D$ and $D^{*}$ of $\mathfrak{C}$;
</li>
  <li> a morphism $\mathsf{coev}:\mathbf{1}\longrightarrow D\otimes D^{*}$; and
</li>
  <li> a morphism $\mathsf{ev}:D^{*}\otimes D\longrightarrow\mathbf{1}$
</li>
</ul>
satisfying the triangle identities:

<img width = "450" src = "http://math.ucr.edu/home/baez/mathematical/ACT2020/Lessard/triangle_id.png" alt = ""/>

This data suggests a presentation $(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0)$ for a $\mathsf{PROP}$, in particular the <b>free dual pair</b>. We set:
<ul>
  <li> $\mathbf{X}_0 = \{D,D^\star\}$;
</li>
  <li> $\mathbf{X}_1 = \{
        \mathsf{coev}:() \longrightarrow (D,D^{\star}), 
        \mathsf{ev}:(D^{\star},D)\longrightarrow ()
    \}$; and
</li>
  <li> $\mathbf{R} =
    \Big\{
        \big(
          (D,\mathsf{ev}) \circ (\mathsf{coev},D) , \mathrm{id}_{D}
        \big),
        \ 
        \big(
          (\mathsf{ev},D^{\star})\circ(D^{\star},\mathsf{coev}) , \mathrm{id}_{D^{\star}}
        \big)
    \Big\}$
    <!--
      $\mathbf{R} =
    \{
        \mathsf{triangle}:(D,\mathsf{ev}) \circ (\mathsf{coev},D) = \mathrm{id}_{D}, \ 
        \mathsf{triangle}^{\star}:(\mathsf{ev},D^{\star})\circ(D^{\star},\mathsf{coev}) = \mathrm{id}_{D^{\star}}
    \}$
    -->
</li>
</ul>


### The type theory of the free dual pair

We will now develop the rules of the type theory for the free dual pair from the data this presentation $\left(\mathbf{R},\mathbf{X}_1,\mathbf{X}_0\right)$. While we have not bothered with them until now, Shulman's practical type theory does include rules for term formation. In the case of the practical type theory for the free dual pair, the rules for the term judgment are few. We present a streamlined version of them:
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{solid}
                    \colalign{center}
                  }
(x:A) \in\Gamma \\
\Gamma\vdash x \; \mathsf{term}
}
\qquad

\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{solid}
                    \colalign{center}
                  }
1\leq k \leq 2 \\
\mathsf{coev}_{(k)}\; \mathsf{term}
}

\qquad

\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{solid}
                    \colalign{center}
                  }
\Gamma\vdash m \;\mathsf{term} \quad \Gamma\vdash n \;\mathsf{term}\\
\Gamma\vdash\mathsf{ev}(m,n)\; \mathsf{term}
}
\]
The first rule is the usual variable rule which gives us the terms in which we may derive the typing judgments corresponding to identities. The second one gives us terms in which we may derive co-evaluation as a typing judgment. Finally, the last one gives us the terms in which we may derive evaluation as a typing judgment.

For the typing judgments, we have two (again slightly streamlined) rules:
<ul>
      <li> the so-called <b> generator rule </b>
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{none none solid}
                    \colalign{center}
                  }
\Gamma \in
\left(
  \overrightarrow{p},\dots,\overrightarrow{q},\overrightarrow{r}\left|\overrightarrow{z}\right.
\right)
:
\left(
  \overrightarrow{C},\dots,\overrightarrow{D},\overrightarrow{E}
\right)\\
        h:\overrightarrow{C} \rightarrow () \in \mathbf{X}_1 \quad \dots \quad k:\overrightarrow{D} \rightarrow () \in \mathbf{X}_1\\
         \sigma : \left(\overrightarrow{F},\dots,\overrightarrow{G},\overrightarrow{E}\right) \overset{\sim}{\longrightarrow} \bigtriangleup\in \Sigma_{\mathbf{X}_0}
\tau \in \mathsf{Shuffle}
\left(
  h,\dots,k; \overrightarrow{z}
\right)\\
\Gamma \vdash
\left(
  \left.
  \sigma
  \left(
    \overrightarrow{f}
    \left(
      \overrightarrow{m}
    \right)
    , \dots,\overrightarrow{g}
    \left(
      \overrightarrow{n}
    \right)
    ,  \overrightarrow{r}
    \right)
    \right|
      \tau
      \left(
        h
        \left(
         \overrightarrow{p}
        \right)
        ,\dots, k
        \left(
          \overrightarrow{p}
        \right)
        , \overrightarrow{z}
      \right)
  \right)
}
\]
        corresponds to applying a tensor product followed by a braiding $\sigma$ and a shuffling of scalars. The tensor product is taken between generating scalar-valued functions $h,\dots,k$ (which can only be some number of copies of $\mathsf{ev}$ in our case) and the identity on some object, here $\overrightarrow{E}$. And, </li>

        <li> the so-called <b> identity rule </b>
            
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{none solid}
                    \colalign{center}
                  }
        f:() \rightarrow \overrightarrow{B} \in \mathbf{X}_1 \quad \dots \quad g:() \rightarrow \overrightarrow{C} \in \mathbf{X}_1 \\
         \sigma:\left(
                    \overrightarrow{A},
                    \overrightarrow{B},
                    \dots,
                    \overrightarrow{C}
                    \right) \overset{\sim}{\longrightarrow} \bigtriangleup \in \Sigma_{\mathbf{X}_0} \\
\overrightarrow{x}:\overrightarrow{A} \dashv
\left(
  \left.
  \sigma
  \left(
    \overrightarrow{x},\overrightarrow{f},\dots,\overrightarrow{g}
  \right)
  \right|
    h,\dots,k
  \right):\bigtriangleup}
\]
            which corresponds to applying a braiding $\sigma$ to the tensoring of some number of generating constants, here $f,\dots,g$ (which can only be some number of copies of $\mathsf{coev}$), and the identity on some object $\overrightarrow{A}$.</li>
</ul>

<strong> Remark. </strong> Here we are ignoring the notion consideration of ``activeness'', a technical device introduced to rigidify the type theory into one with unique derivations of judgments by providing a canonical form for 1-cells. We also ignored the syntactic sugar of labels, which act like formal variables for the unit type.



Lastly, for the equality judgment we have axioms
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{solid}
                    \colalign{center}
                  }
        \left(
          (D,\mathsf{ev})
          \circ
          \left(
            \mathsf{coev},D
          \right)
          ,
          \mathrm{id}_{D}
        \right)
         \in \mathbf{R} \\
         m:D \vdash \left(\mathsf{coev}_{(1)} \left|
         \mathsf{ev}\left(\mathsf{coev}_{(2)},M\right)
         \right.\right) = m:D 
}
\]
and
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{solid}
                    \colalign{center}
                  }
  \left(
    ( \mathsf{ev} , D^{\star})
    \circ
    \left(
      D^{\star},\mathsf{coev}
    \right)
    ,
    \mathrm{id}_{D^{\star}}
  \right)
  \in
  \mathbf{R}  \\
  n:D^{\star} \vdash 
  \left(
    \mathsf{coev}_{(2)} \;
    \left|
      \; \mathsf{ev}
      \left(
        N,\mathsf{coev}_{(1)}
      \right)
    \right.
  \right)
  = n:D^{\star}
}
\]
together with enough rules so that $=$ acts as a congruence relative to all of the other rules.

<strong> Example. </strong> Consider the composition
\[
    (D)\xrightarrow{\left(\mathsf{coev},D\right)} \left(D,D^{*},D\right) \xrightarrow{\left(D,\mathsf{ev}\right)} (D)
\]
which  corresponds to the typing judgement
\[
    x:D\vdash \left(\mathsf{coev}_{(1)}|\mathsf{ev} \left(\mathsf{coev}_{(2)},x\right)\right)
\]
This typing judgement admits the following derivation
\[
\array{ \arrayopts{ \frame{none} 
                    \rowalign{bottom} 
                    \rowlines{solid}
                  }                    
        \array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{solid}
                    \colalign{center}
                  }
        \mathsf{coev}:() \rightarrow (D,D^{\star}) \in \mathbf{X}_1 & (132):
        \left(
          D,D,D^{\star}
        \right)
        \overset{\sim}{\longrightarrow}
        \left(
          D,D^{\star},D
        \right)
        \\
        \cellopts{\colspan{2}} x:D\vdash
        \left(
        \mathsf{coev}_{(1)},\mathsf{coev}_{(2)},x
        \right):D 
}

& \mathsf{ev}: \left(D^*,D\right) \rightarrow () \in \mathbf{X}_1

\\

\cellopts{\colspan{2}} x:D\vdash
\left(
  \left.
    \mathsf{coev}_{(1)}
  \right|
  \mathsf{ev}
  \left(
          \mathsf{coev}_{(2)},x
  \right)
\right)
}
\]
where:
<ul>
  <li> the first rule is an instance of the identity rule with premised generators $\mathsf{coev}$ and the braiding $(132)$; and</li>
  <li> the second rule is an instance of the identity rule with the typing judgement $$x:D\vdash \left(\mathsf{coev}_{(1)},\mathsf{coev}_{(2)},x\right):D$$ the consequent of the first rule and the additional hypothesis being the generator $\mathsf{ev}$.
</li>
</ul>


### "Elements" of dual objects

We have now developed a type theory for the free dual pair which endows
the dual objects $D$ and $D^{\star}$ with a universal notion of element (that of $D$-typed term and $D^{\star}$-typed term respectively).
Since the notion of dual pair abstracted the instance of a pair of
dual vector spaces, which in particular have actual elements, it behooves
us to ask:

<b>``to what extent is term of type $D$ like a vector (in $D$)?'' </b>

The answer is both practical and electrifying (though perhaps the
authors of this post are too easily electrified).

It's easy enough to believe that the evaluation map 
\[
\mathsf{ev}:\left(D,D^{\star}\right)\longrightarrow ( )
\]
 endows the terms of type $D$, or $D^{\star}$ for that matter, with a structure of scalar valued functions on the other. The triangle identities impose the unique determination of terms of type $D$ or $D^{\star}$ in terms of their values as given by $\mathsf{ev}$.  Indeed consider that, for a finite dimensional vector space $V$ over a field
$k$, a basis $\{ \mathbf{e}_{i}\}_{i=1}^{n}$ for $V$ and a dual basis $\{ \mathbf{e}_{i}^{\star}\}_{i=1}^{n}$ for $V^{\star}$ give us an elegant way to write $\mathsf{coev}$ and the
first triangle identity. We write
\[
\begin{aligned}
k & \overset{\mathsf{coev}}{\rightarrow} V\otimes V^{\star}\\
x & \mapsto \sum_{i=1}^{n}\mathbf{e}_{i}\otimes\mathbf{e}_{i}^{\star}
\end{aligned}
\]
and see that

<img width = "450" src = "http://math.ucr.edu/home/baez/mathematical/ACT2020/Lessard/dual_pair.diag.png" alt = ""/>

The observation for dual vector spaces
\[
    V \mathrm{ and } V^{\star}=\mathsf{Hom}_{\mathsf{Vect}_k}(V,k )
\]
that the triangle identities hold is just the observation that a vector is precisely determined by its values: every vector $\mathbf{v}$  is equal to the un-named vector
\[
\sum_{i=1}^{n}\mathbf{e}_i^{\star}( \mathbf{v})\cdot \mathbf{e}_i
\]
which is defined by taking the values $\mathbf{e}^\star_{i}( \mathbf{v} )$ at the dual vectors $\mathbf{e}_i^{\star}$.
As part of the definition of a dual pair in an arbitrary symmetric strict monoidal category then, the triangle identities imposes this as a relationship between $\mathsf{ev}$ and $\mathsf{coev}$. But within type theory, this sort of relationship between an un-named function and its values is familiar, indeed it is something very much like $\beta$-reduction.

To see this more clearly, let us make a pair of notational changes. In place of writing 
\[
(x,y)
:
\left(
  D^{\star},D
\right)
\vdash
\mathsf{ev}(x,y):()
\]
we will denote $\mathsf{ev}$ infix by $\triangleleft$ and write
\[
(x,y)
:
\left(
  D^{\star},D
\right)
\vdash x\triangleleft y:().
\]
Similarly, in place of writing 
\[
\vdash \left( \mathsf{coev}_{(1)},\mathsf{coev}_{(2)} \right):\left(D,D^{\star}\right)
\]
 we will denote $\mathsf{coev}$ by the pair $\left(u,\lambda^{D}u\right)$
and write
\[
\vdash\left(u,\lambda^{D}u\right):\left(D,D^{\star}\right).
\]
With this choice of notation then, the equality judgment which corresponds to
the first triangle identity is 
\[
x:D\vdash\left( u \; \left| \; \lambda^{D}u\triangleleft x\right.\right)=x:D.
\]

Then, since $=$ is a congruence with respect
to substitution (recall that we promised that the rules for the equality judgement were precisely those  required for generating a congruence from a set of primitive relations), if we have, for some term $m$, the term $\lambda^{D}u\triangleleft m$
appearing in the scalars of a list of terms, then we may replace all
instances of $u$ in the rest of the term with $m$. While a mouthful,
this is a sort of "$\beta$-reduction for duality" allowing us to treat $\mathsf{coev}$ as a sort of $\lambda$-abstraction, as we suggested by the change in notation. Conceptually interesting in its own right, this observation also yields a one line
proof for a familiar theorem, namely the cyclicity of the trace.

<strong> Example. </strong>
Consider two dual pairs 
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{none}
                  }
\left(A,A^{*},\left(u,\lambda^{A}u\right),-\triangleleft -\right)
&\qquad \qquad&
\left(B,B^{*},\left(v,\lambda^{B}v\right),- \triangleleft -\right)
}
\]
in a symmetric strict monoidal category $\big(\mathfrak{C},(-, -),()\big)$
and a pair of maps $f:A\longrightarrow B$
\[
()\overset{(v,\lambda^{B}v)}{\longrightarrow} \left(B,B^{\star}\right)\overset{f\circ g}{\longrightarrow} \left(B,B^{\star}\right)\overset{(12)}{\longrightarrow} \left(B^{\star},B\right)\overset{ - \triangleleft -}{\longrightarrow} ()
\]
where $(12)$ denotes the permutation of entries of the list. Likewise the trace $\mathsf{tr}\left(g\circ f\right)$ is the composition.
\[
()\overset{(v,\lambda^{A}v)}{\longrightarrow} \left(A,A^{\star}\right)\overset{g\circ f}{\longrightarrow} \left(A,A^{\star}\right)\overset{(12)}{\longrightarrow} \left(A^{\star},A\right)\overset{ - \triangleleft -}{\longrightarrow} ()
\]
Using the notation introduced above it follows that $\mathsf{tr}\left(f\circ g\right)=\mathsf{tr}\left(g\circ f\right)$ as:
\[
\array {\arrayopts{ \frame{none} 
                    \rowalign{top} 
                    \rowlines{none}
                    \colalign{right left left }
                  }
\mathsf{tr}(f\circ g) & \overset{\mathsf{def}}{=}
&
\left(
  \left|
    \lambda_{u}^{B}\triangleleft f\big( g(u) \big)
  \right.
\right)
\\

 & = &

\left(
  \left|
    \lambda_{u}^{B}\triangleleft f(v),\lambda_{v}^{A}\triangleleft g(u)
  \right.
\right)
\\

& = &

\left(
  \left|
    \lambda_{v}^{A}\triangleleft g\big(f(v)\big)
  \right.
\right)
\\

 & \overset{\mathsf{def}}{=} & \mathsf{tr}(g\circ f)
}
\]
Where the judged equalities are applications of "$\beta$-reduction for a duality".

