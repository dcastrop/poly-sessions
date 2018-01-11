# Session Type Extraction from Recursion Pattern

See [ToDo](#todo) list for current progress.

***WARN: using LaTeX code for sketching the definitions. Rendered in GitLab.***
***FIXME: math symbols in KaTeX are a bit limited ...***

Ideas:

* **Problem**: high-level programming models greatly simplify the development of
  parallel software. These models rely on programming using a set of fixed,
  predefined constructs that implement common parallel programming structures.
  This fixed set of constructs, although very general, lack flexibility in that
  it is generally not easy to add new parallel structures.


* **Idea**: We propose an alternative approach that, unlike common high-level
  parallel programming models, is not constrained to a predefined set of
  parallel constructs. Our approach is based on the theory of _Multiparty
  Session Types_, that allow the specification of a pattern of communication
  between components. In this work, we extract potential __communication
  protocols__ from recursive functions.  Moreover, the extraction process
  determines how to instantiate the parallel structure with sequential code to
  produce a final parallel program.

* **(tentative) Contributions**:
  1. Automatic extraction of potential parallel structures from recursive
  functions as _global session types_.
  2. Generate _parallel implementations_ specifically tailored to a program,
  that we can guarantee _deadlock-free_.
  3. Semi-automatic and _sound_ parallelisation of sequential functions.
  4. Relate _parameterised multiparty session types_ to _algebraic datatypes +
  traversals_?

## Contents

```
poly-session
├── app ························ Command-line application
│   └── Main.hs ···················· Main
├── src ························ Library
│   ├── Base ······················· Basic definitions
│   │   ├── Id.hs ······················ Names and identifiers
│   │   └── PrimTypes.hs ··············· Primitive types
│   └── Language ··················· Rewritings and Language defs
│       ├── PolySession.hs ············· MPST generation from Polynomial functors
│       └── SessionTypes.hs ············ Deep-embedding of a MPST language
└── test ······················· Directory of the main test suite
    └── Spec.hs ···················· Tests
```

## Parallel Strategies as MPST Topologies

Parallel strategies are in direct correspondence with higher-order functions
that implement the relevant [pattern of
parallelism](#relation-to-algorithmic-skeletons).  MPST topologies require:
entry point/exit point. In case of a reduce, multiple entry points means that we
need to do data distribution before session starts.


## From Recursion Schemes to MPST Topologies

***TODO: assumptions, invariants, etc***

* There is one special participant, the 'master', that first sends a/many
  value/s, and then expects a/many response/s.
* All workers in a global type must receive a value, followed by a number
  of request/response interactions, and finally do their own response to the
  original sender.

### Tree-like Algebraic Datatypes as Polynomial Functors

```math
\begin{array}{rcll}
F, G\; \in\; \mathsf{Poly}^n & ::= & X          & \text{(variable)} \\
                       &  |  & \Pi_i        & \text{(projection)} \\
                       &  |  & \mathsf{K}_A & \text{(constant)} \\
                       &  |  & F + G        & \text{(coproduct of functors)} \\
                       &  |  & F \times G   & \text{(product of functors)} \\
                       &  |  & \mu\; X. F   & \text{(recursive functor)}
\end{array}
```

The treatment of polynomial functors follows is standard in the generic
programming community. We define a family of polynomial _n_-endofunctors,
indexed by the natural number _n_.

Informally, the semantics of the different constructs is:

```math
\begin{array}{rcl}
\Pi_i\, A_1 \cdots A_m & = &
  A_i \qquad \Leftarrow 1 \le i \le m \\

\mathsf{K}_A\, A_1 \cdots A_m & = &
  A \\

(F + G)\,A_1 \cdots A_m & = &
  F\, A_1\cdots A_m +  G\, A_1\cdots A_m \\

(F \times G)\,A_1 \cdots A_m & = &
  F\, A_1\cdots A_m \times  G\, A_1\cdots A_m \\

(\mu\; X. F) A_1 \cdots A_m & = &
  F[(\mu\; X. F) / X]\, A_1\cdots A_m
\end{array}
```

**Example 1**:

The Haskell algebraic datatype

```Haskell
data Ty a b = C1 | C2 a (Ty a b) | C3 b (Ty a b) (Ty a b)
```
corresponds to the following polynomial:

```math
\mu\,\mathtt{Ty}.\;
  \mathsf{K}_{()} +
  \Pi_a \times \mathtt{Ty} +
  \Pi_b \times \mathtt{Ty} \times \mathtt{Ty}
```

**Example 2**:

The below Haskell algebraic datatype **cannot** be represented in
$`\mathsf{Poly}`$. This would require function types, which would mean we would
need to handle exponentials.  Moreover, `Ty` is a bifunctor, covariant in `b`,
and contravariant in `a`, which is also not possible to represent in
$`\mathsf{Poly}`$.  ***Hint***: _there is a paper on catamorphisms on datatypes
with functions. May be worth checking_.

```Haskell
data Ty a b = C1 (a -> b) | C2
```

### Polynomial Functors to MPST topologies

The translation from $`\mathsf{Poly}`$ to $`\mathsf{MPST}`$ must ensure that the
semantics of a pattern of recursion in $`\mathsf{Poly}`$ is preserved, when
implemented using the corresponding MPST topology.  *TODO: this should be
formally stated somewhere.*


Considerations. For all generated topologies:

   1. There should be three separate phases in the generated types: data
      distribution, (possibly) computation, and data collection.
   2. Two different participants should handle distribution and collection.  The
      idea behind this is to decouple the "sends" from "receives". But this will
      force the sender to synchronise with the receiver (*not sure how yet*)
   3.


#### Maps on Polynomials

The simplest possible approach is to generate, for a polynomial _n_-functor, _n_
different topologies that correspond to parallel processes in charge of the
_map_ operation.

--------------------------------------------------------------------------------
**Example 3**:

A list datatype, `data [a] = [] | a : [a]` corresponds to:
```math
\mu\; L. \mathsf{K}_{()} + \Pi_a \times L
```

Multicast taken from:
[_Global Progress for Dynamically Interleaved Multiparty Sessions_][2], and
syntax of multiparty/local session types is taken from
[_A Linear Decomposition of Multiparty Sessions..._][3].

The pattern is the following. Given a collection of workers
$`W_1, W_2, \ldots, W_n : \mathsf{Role}`$, and two distinct roles $`I`$ and $`O`$:
```math
\begin{array}{l}
\mathtt{iter} : \mathsf{Role}\times\mathsf{Role}\times\mathsf{Role}^n \to
                (\mathsf{Role}^n\to\mathsf{Role}) \times \mathsf{Protocol} \to
                \mathsf{Protocol} \\
\mathtt{iter}\; (I, O, W)\; (\pi_i, P) = \\
\qquad I \to \{Ws, O\} :
  \left\{\begin{array}{l}
    l_1(\mathsf{unit}) : \mathsf{end} \\
    l_2(\mathsf{unit}) : I \to (\pi_i\;W) : d(a). (\pi_i\;W) \to O : d(b). P
  \end{array}\right.
\end{array}
```

Global protocol for _map_ operations:
```math
\begin{array}{l}
\mathtt{listProto} : \mathsf{Role}\times\mathsf{Role}\times\mathsf{Role}^n \to
                     \mathsf{Protocol} \\
\mathtt{listProto}\; (I,\; O,\; W) :=
  \mathtt{let}\;\mathtt{iterf} = \mathtt{iter}\; (I, O, W)\; \mathtt{in} \\
  \quad \mu\; X. \mathtt{iterf}(\pi_1,
                   \mathtt{iterf}(\pi_2,
                     \ldots
                       \mathtt{iterf}(\pi_n, X)\ldots))
\end{array}
```

**ISSUES:** from a parallel programming perspective, this global type is far
from ideal. The messages to every participant means that the processes will
run in lock-step. Besides, if the order of the messages is irrelevant (which
is good for achieving speedups parallelising irregular applications), then this
MPST forces a _round robin_ scheduling mechanism, which will not achieve good
load-balancing. *Question for future:* is there any theory of
MPST that can be used message-passing primitives that work using
_shared intermediate buffers_. This would match more closely message-passing
constructs for concurrency in a number of languages: e.g. Go (channels
are essentially shared buffers).

**Example**: Given $`W_1`$ and $`W_2`$,
```math
\mathtt{listProto}\; (I, O, W_1, W_2)\; =
  \mu\; X.\; I \to \{W_1, W_2, O\} :
  \left\{\begin{array}{ll}
    l_1() . & \mathsf{end} \\
    l_2() . & I \to W_1 : d(a), \\
            & W_1 \to O : d(b), \\
            & I \to \{W_1, W_2, O\} : \\
            & \quad\left\{\begin{array}{l}
                     l_1()\; .\; \mathsf{end} \\
                     l_2()\; .\; I \to W_2 : d(a)\; .\; W_2 \to O : d(b)\;.\; X
                 \end{array}\right.
  \end{array}\right.
```

Role $`I`$ is the _emitter_ process (terminology taken from [Fastflow][1]). It
is in charge of distributing the data, and has the following local type:
```math
I := \mu\; X.\; W_1\; \oplus\; !\;
  \left\{\begin{array}{ll}
     l_1()\; . & W_2\; !\; l_1()\; .\; O\; !\; l_1()\; .\; \mathsf{end} \\
     l_2()\; . & W_2\; !\; l_2()\; .\; O\; !\; l_2()\; .\; W_1\; !\; d(A)\; .
       W_1\; \oplus\; !\;
         \left\{\begin{array}{ll}
           l_1()\; . & W_2\; !\; l_1()\; .\; O\; !\; l_1()\; .\; \mathsf{end} \\
           l_2()\; . & W_2\; !\; l_2()\; .\; O\; !\; l_2()\; .\;
              W_1\; !\; d(A)\; . X
         \end{array}\right.
   \end{array}\right.
```

Roles $`W_i`$ are the workers of the parallel process:
```math
W_1 := \mu\; X.\; I\; \&\;?\;
  \left\{\begin{array}{ll}
     l_1()\; . & \mathsf{end} \\
     l_2()\; . & I\; \&\;? d(A)\;.\; O\; !\; d(B)\; .\; I\; \&\;?\;
       \left\{\begin{array}{ll}
         l_1()\;. & \mathsf{end} \\
         l_2()\;. & X
       \end{array}\right.
   \end{array}\right.
```

```math
W_2 := \mu\; X.\; I\; \&\;?\;
  \left\{\begin{array}{ll}
     l_1() & .\; \mathsf{end} \\
     l_2() & .\; I\; \&\;?\;
       \begin{array}{ll}
          l_1() & .\; \mathsf{end} \\
          l_2() & .\; I\; ?\; d(A)\; .\; O \; !\; d(B)\; .\; X
       \end{array}
   \end{array}\right.
```

Role $`O`$ is the _collector_ process (terminology taken from [Fastflow][1]). It
is in charge of gathering the data, and has the following local type:
```math
O := \mu\; X.\; I\; \&\;?\;
  \left\{\begin{array}{ll}
     l_1() & .\; \mathsf{end} \\
     l_2() & .\; W_1 \;?\; d(B)\; .\; I\; \&\;?\;
       \left\{\begin{array}{ll}
         l_1() & .\; \mathsf{end} \\
         l_2() & .\; W_2\;\&\;?\; d(B)\;.\; X
       \end{array}\right.
  \end{array}\right.
```

**TODO: find a more compact way of doing this. E.g. something on the lines of:**
```math
L := \forall i \in [1\ldots n], \mu\; X. I \to \{W, O\} :
  \left\{\begin{array}{l}
    l_1 : \mathsf{end} \\
    l_2 : I \to W[i] : a, W[i] \to O : b, X
  \end{array}\right\}

```

--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
**Example 4**:

A tree datatype, `data Tree a b = Leaf a | Node b (Tree a) (Tree a)` corresponds
to:
```math
\mu\; T. \Pi_{a} + \Pi_b \times T \times T
```
**TODO**: generate "tree-like emitters and collectors", plus "map workers".

**Update 28/11/2017: from this point on, this is out of date.**

There are three suitable MPST topologies for this functor:

```math
T_a = \mu\; T. M \to W : \left\lbrace
    \begin{array}{l}
            T_1 : \mathsf{end} \\
            T_2 : M \to W : \langle a \rangle, W \to M : \langle c \rangle, T
    \end{array}\right.
```

```math
T_b = \mu\; T. M \to W : \left\lbrace
    \begin{array}{l}
            T_1 : \mathsf{end} \\
            T_2 : M \to W : \langle b \rangle, W \to M : \langle d \rangle, T
    \end{array}\right.
```

```math
T_{ab} = \mu\; T. M \to W : \left\lbrace
    \begin{array}{l}
            T_1 : \mathsf{end} \\
            T_2 : M \to W : \langle a \rangle, W \to M : \langle c \rangle,
                  M \to W : \langle b \rangle, W \to M : \langle d \rangle, T
    \end{array}\right.
```

#### A First Attempt


This is a naive translation scheme. ***FIXME***: this should not work yet (at
least not without restricting the syntax of $`\mathsf{Poly}`$).

```math
\begin{array}{rcl}
\mathsf{mpst}(Gf, \overline{A}, X) & = & \\

\mathsf{mpst}(Gf, \overline{A}, \Pi_i) & = & \\

\mathsf{mpst}(Gf, \overline{A}, \mathsf{K}_A) & = & \\

\mathsf{mpst}(Gf, \overline{A}, F + G) & = &
  R \to F : \lbrace \mathsf{mpst}(Gf, \overline{A}, F) -> R :
              \langle \overline{A} \rangle,
              \mathsf{mpst}(Gf, \overline{A}, G) -> R :
              \langle \overline{A} \rangle,
              R -> M : \langle F\; \overline{A} + G\; \overline{A} \rangle
            \rbrace \\

\mathsf{mpst}(Gf, \overline{A}, F \times G) & = &
  \mathsf{mpst}(Gf, \overline{A}, F) -> R : \langle \overline{A} \rangle,
  \mathsf{mpst}(Gf, \overline{A}, G) -> R : \langle \overline{A} \rangle,
  R -> M : \langle F\; \overline{A} + G\; \overline{A} \rangle \\

\mathsf{mpst}(Gf, \overline{A}, \mu\; X. F)
  & = & \\
\end{array}
```

### Polynomial *Primitives* to Session Types

* Given a function $`f : T_1 \to T_2`$, start with two roles, A and B, and a
  simple protocol:

```math
A \to B : T1 .{B \sim f}. B -> A : T2.
```

Then, "rewrite" the protocol, depending on `f`, and the types $`T_1`$ and
$`T_2`$.

```
 >>> Problem: in a hylo, we want to further decompose this, but the types might
 >>> tell you nothing of internal structure. We need to "peek" at the function
 >>> "f", and start decomposing it. First into "cata/anamorphism", then extract
 >>> "maps". Then apply rules:

Sum-type decomposition:

A -> B : T1 + T2 + T3. G ----->


A -> {B1, B2, B3} + R : { l1 : A -> B1 : T1. G[B1\B]
                        , l2 : A -> B2 : T2. G[B2\B]
                        , l3 : A -> B3 : T3. G[B3\B] }

R is any role in G that is not A or B.

B must compute something of this shape: f = f_1 \/ f_2 \/ f_3
B1 B2 B3 therefore compute f_1 f_2 and f_3 respectively
Any role receiving the response from B will know where to receive from thanks to
the label 'l1', 'l2' or 'l3'.

*** Product-type decomposition:

A -> B : T1 x T2 x T3. G --->

A -> B1 : T1. A -> B2 : T2. A -> T3 : B3. G[{B1, B2, B3}\ B]

The substitution: G[{B1, B2, B3}\ B]

must deal with 'B' on the sender side:

B -> C : T [{B1, B2, B3} \ B] ====>
    B1 -> C' : T1. B2 -> C': T2, B3 -> C' : T3


B must therefore compute "T1 x T2 x T3 -> T1' x T2' x T3' -> T"

  f = g . f1 x f2 x f3

Computation 'g' is moved to 'C', f1, f2 and f3 are done in parallel by B1, B2
and B3.

*** Recursion:

For recursive types, apply isomorphism and continue using rules for sums and
products:

A -> B : mu X. T ==> A -> B : T [mu X. T / X]

mu X. T ==> T (mu X. T)


1 + A x (1 + A x L) ~~ 1 + A + A x A + A x A x A x L

mu L . m -> {w1 w2 w3} : { l1 : end
                         , l2 : m -> w1 : A, w1 -> m : B. end
                         , l3 : m -> {w1,w2} : A, {w1,w2} -> m : B. end
                         , l3 : m -> {w1, w2, w3} : A.
                                {w1, w2, w3} -> m : B. L }

A + X  ~~~ A + A + A + X


mu L . m -> {w1 w2 w3} : { l1 : m -> w1 : A. w1 -> m : B. end
                         , l2 : m -> w2 : A. w2 -> m : B. end
                         , l3 : m -> w2 : A. w3 -> m : B. end
                         , l4 : L }
```

##### A Deep Embedding of a MPST Theory

**TODO**: Extend to parameterised when needed:

```Haskell
type Role  = Int
type Label = Int

data GProtocol =
   Rec (GProtocol -> GProtocol)
 | End
 | Msg [Role] [Role] Branch

data Branch =
   BMsg GProtocol
 | BBr  [(Label, GProtocol)]
```


## Relation to Algorithmic Skeletons

One succesful high-level model for parallel programming is structured parallel
programming using algorithmic skeletons. Algorithmic skeletons are
implementations of common patterns of parallelism, such as the common *map* and
*reduce* operations. However, parallelising sequential functions using
algorithmic skeletons requires to:

  a) derive a high-level parallel structure of a program; and,
  b) instantiate the parameters of the algorithmic skeletons with the necessary
  parameters.

Unlike the session type approach, algorithmic skeletons rely on the existence of
a predefined set of implementations for the parallel patterns.

## Examples
The approach is illustrated with the following examples, coded in Haskell
syntax, using uncurried functions:

- [ ] Dot product
- [ ] FFT
- [ ] N-Body (naive)
- [ ] N-Body (Barnes-Hut)
- [ ] Black-Scholes
- [ ] K-Means
- [ ] Lineq
- [ ] Heat equation
- [ ] Wordcount
- [ ] AdPredictor

### Completed

### Sketched

#### Dot Product

Dot product has a simple implementation in terms of patterns of recursion:

```Haskell
dot :: ([Float], [Float]) -> Float
dot (x, y) = fold ((+), 0, map ((*), zip (x ,y)))
```

##### Breaking Down a Haskell Implementation

Preliminaries: recursive structure of dotproduct
The dot product can be split into 3 different parts:

```Haskell
dot_split :: ([Float], [Float]) -> [(Float, Float)]
dot_split = zip

dot_map :: [(Float, Float)] -> [Float]
dot_map l = map ((*), l)

dot_fold :: [Float] -> Float
dot_fold l = fold ((+), 0, l)

-- Stages: ([Float], [Float]) |unfold> [(Float, Float) |map> Float] |fold> Float
dot :: ([Float], [Float]) -> Float
dot = dot_fold . dot_map . dot_split
```

A fold corresponds to a catamorphism, where the base list functor, in Haskell,
is `L`, shown below:
```Haskell
fold (op, z, l) = cata (const z :+: op)

newtype L a b = L (Maybe (a, b))

instance Base L [] where
  inf :: L a [a] -> [a]
  inf Nothing = []
  inf Just (h, t) = h::t

  outf :: [a] -> L a [a]
  outf [] = Nothing
  outf (h:t) = Just (h,t)
```

```Haskell
cata :: Base f g => forall a b. (f a b -> b) -> g a -> b
cata f = f . bimap (id, cata_f) . outf
  where cata_f = cata f
```

List reduce:

```Haskell
newtype T a b = T (Either (Maybe a) (b, b))

inT :: T a [a] -> [a]
inT (Left Nothing)  = []
inT (Left (Just x)) = [x]
inT (Right t)       = append t

outT :: [a] -> T a [a]
outT []  = Left Nothing
outT [x] = Left (Just x)
outT xs  = Right (split xs)
  where split l = (take (length l `div` 2) l, drop (length l `div` 2) l)

-- Note that by factoring out the `reshaping`, reduce becomes a `cata`
reduce :: forall a b. (T a b -> b) -> [a] -> b
reduce f = f . bimap (id, reduce_f) . outL
  where reduce_f = reduce f
```

Dot-fold can be rewritten to use a reduce, because (+) is associative:
```Haskell
dot_fold :: [Float] -> Float
dot_fold l = fold ((+), 0, l)

dot_reduce :: [Float] -> Float
dot_reduce l = reduce f l
  where f (Left Nothing)  = 0
        f (Left (Just x)) = x
        f (Just (a, b))   = a + b

-- forall l, dot_fold l = dot_reduce l, because (+, 0) forms a monoid
```

The recursive structure of `dot_reduce` is therefore that of `reduce`, or:
```Haskell
-- type Tree a =  Mu (T a)
-- isomorphic to:
data Tree a = Empty | Leaf a | Node (Tree a) (Tree a)
```

##### Generating a Multiparty Protocol from the Recursive Structure of `dot`

The idea is to map constructors to unique participants. Each participant
represents a process that is in charge of doing a reduction. From a multiparty
perspective, we need a static "process network" that is capable of handling
multiple shapes of `Tree`. Each participant in that protocol contains a
sub-tree, and forwards a value, the result of the computation, to the "parent
node". If we want a degree of parallelism of "n", this implies handling trees of
depth "n":

```Haskell
data Tree a = Empty | Leaf a | Node (Tree a) (Tree a)

data TreeShape = Empty_Leaf' Int | Node' Int Tree_Shape Tree_Shape
```

### Examples To Consider


#### FFT
#### N-Body (naive)
#### N-Body (Barnes-Hut)
#### Black-Scholes
#### K-Means
#### Lineq
#### Heat equation
#### Wordcount
#### AdPredictor

## To-Do

* Technical development:
- [ ] Polynomial expressions to MPST (considering adding annotations tagging
  roles to functions in interactions).

* Implementation:
- [ ] Deep-embedding of expressions in Poly

* Examples:

- [ ] Dot product
- [ ] FFT
- [ ] N-Body (naive)
- [ ] N-Body (Barnes-Hut)
- [ ] Black-Scholes
- [ ] K-Means
- [ ] Lineq
- [ ] Heat equation
- [ ] Wordcount
- [ ] AdPredictor


[1]: http://calvados.di.unipi.it/
[2]: https://doi.org/10.1017/S0960129514000188
[3]: http://dx.doi.org/10.4230/LIPIcs.ECOOP.2017.24
