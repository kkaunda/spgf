---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

Let us lean together!
![]({{ site.repository_url }}?raw=true/vertopal_bfea56392a264e1da44fa95b98b2549d/media/image2.jpeg)

Welcome: Project status: work in progress.

In this open community project, we formalize using the LEAN programming
language, the definitions and results presented in the paper [*Structure
in Prime Gaps*](https://www.researchsquare.com/article/rs-4058806/latest).

Formalization of Mathematics.

The formalization of mathematics refers to the process of encoding
mathematical definitions, theorems, and proofs in a formal language that
can be processed and checked for correctness by a computer. This
approach ensures that every logical step is explicitly verified, leaving
no room for ambiguity or human error. This meticulous approach ensures
that every logical step is explicitly defined and verified, minimizing
the risk of human error in mathematical proofs. The goal is to achieve a
level of rigor and precision that surpasses traditional mathematical
methods, enabling the verification of complex proofs and the discovery
of new mathematical insights. Formalization not only helps in validating
existing results but also provides a robust framework for discovering
new ones.

Proof Assistants.

Proof assistants are software tools designed to aid in the creation and
verification of formal proofs. These tools provide a platform for
writing proofs in a formal language and automatically verifying their
correctness. They offer a rigorous environment where users can construct
proofs interactively or automatically, depending on the complexity of
the problem. These tools are essential in modern mathematics and
computer science, allowing for the development of highly reliable
software and the verification of intricate mathematical theorems.
Popular proof assistants include Coq, Isabelle, and Lean. There are many
others. They are used not only in pure mathematics but also in fields
like computer science, where formal verification of software and
hardware is crucial. They have been instrumental in formalizing
significant results across various domains.

LEAN.

LEAN is a modern open-source proof assistant developed at Microsoft
Research. It stands out for its user-friendly interface and powerful
capabilities in both theorem proving and automated reasoning. It is
designed to support the formalization of mathematics and the
verification of software. LEAN supports a rich type theory known as
dependent type theory, which allows for expressive and concise
representations of mathematical objects and proofs. Its growing
ecosystem includes a standard library of formalized mathematics and
tools like the LEAN community web editor. LEAN has been adopted by many
mathematicians and computer scientists for both educational purposes and
advanced research projects. LEAN combines powerful automation with
interactive proof development, making it accessible to both beginners
and experts. LEAN 4, the latest version, offers significant improvements
in performance and usability, encouraging more widespread adoption
within the mathematical community.

Structure in Prime Gaps.

In this project, we aim to formalize the results presented in the article
*Structure in Prime Gaps* using LEAN4, the latest version of the LEAN
proof assistant. By leveraging the capabilities of LEAN4, we seek to
ensure the correctness and robustness of these findings relating to the
existence of infinitely many *structured* gaps between prime numbers.
This formalization will provide a rigorous foundation for the results
and contribute to the broader effort of formalizing mathematics.

The paper [*Structure in Prime
Gaps*](https://www.researchsquare.com/article/rs-4058806/latest)
presents two main results the first of which is the claim that there
exist structured gaps between primes and the second result is basically
a corollary or special case of the first. These are stated as follows:

> **Theorem 1**: For every prime *p*<sub>α</sub>, there exists infinitely many
> pairs of primes, (*p*<sub>n</sub>, *p*<sub>n+m</sub>), such that (*p*<sub>n+m</sub> − *p*<sub>n</sub>) =
> *p*<sub>α</sub> − 3, where *n*, *α* ≥ 3, *m* ≥ 1, and *p*<sub>n</sub> is the *n*<sup>th</sup>
> prime.

> **Theorem 2**: There exist infinitely many pairs of primes with a gap of 2.

## A brief visual overview of the results presented in the article *Structure in Prime Gaps*

The following partial Cayley table *T* represents gaps between primes in
which the results we are formalizing are *self-evident*.

Consider Table 1, it is not immediately apparent if any useful pattern
can be discerned from it. However, with the highlights in Table 2, a
compelling *pattern* emerges, one that leads directly to **Theorem 1**
from which **Theorem 2** is implied as seen in Table 3.

-   Each pattern is defined and identified by the 4-tuple *β =* (*A, B,
    L, E*) formed from the elements in the vertices of a sub-array
    *T*<sub>i</sub> of *T*. In Table 2, the first 4-tuple *β =* (*A, B, L, E*)
    for prime 23 is *β =* (20, 28, 12, 20).

-   Every sub-array *TT*<sub>i</sub>, defines two pairs of primes. In Table 2,
    the *First pair* is (3, *p*<sub>α</sub>) or (3, 23) and the *Second pair* is
    (((*B* + 3) + 0 -- *E*), (*B* + 3)) or (11, 31). We can denote the
    integers 11 and 31 in the *Second pair* using the variables *Q*<sub>i</sub>
    and *R*<sub>i</sub> respectively.

-   The *First pair* remains constant for all patterns related to any
    prime *p*<sub>α</sub> ≥ 5. Subsequent *Second pairs* are unique for each
    sub-array *TT*<sub>i</sub> of *T*.

-   *L* is always congruent to 0 mod 6.

**Legend for Tables:**

-   **Table 1:** Represents the Cayley Table *T* of the *Commutative
    Partial Groupoid* structure (*J*, +) without immediately discernible
    patterns highlighted.

-   **Table 2:** Highlights patterns where the 4-tuple *β* = (*A, B, L,
    E*) defines each pattern, with specific examples provided. The
    "Pattern" here is more elaborately defined in the sense that it
    consists of integers other than just *Q*<sub>i</sub> and *R*<sub>i</sub>.

-   **Table 3:** Demonstrates the implication of results derived from
    the patterns observed in Table 2.

-   **Remark:** We note that the Cayley Table *T* is a partial
    representation of an otherwise infinite structure. Therefore no
    generalization of these results to some "complete/larger" set is
    required.

**Table 1**

![]({{ site.repository_url }}?raw=true/vertopal_bfea56392a264e1da44fa95b98b2549d/media/image3.jpeg)

**Table Legend**

![]({{ site.repository_url }}?raw=true/vertopal_bfea56392a264e1da44fa95b98b2549d/media/image4.jpeg)

**Table 2**

![]({{ site.repository_url }}?raw=true/vertopal_bfea56392a264e1da44fa95b98b2549d/media/image5.jpeg)


**Table 3**

![]({{ site.repository_url }}?raw=true/vertopal_bfea56392a264e1da44fa95b98b2549d/media/image6.jpeg)


**Useful Links**

* [Zulip chat for Lean](https://leanprover.zulipchat.com/) for coordination
* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [Doc pages for this repository]({{ site.url }}/docs/)
* Kaunda, K: [*Structure in Prime Gaps*](https://www.researchsquare.com/article/rs-4058806/latest), (2024). (Pre-print).
* Pietro Monticone: [*Lean Project Template*](https://pitmonticone.github.io/LeanProject/) for blueprint-driven formalization projects.
* Patrick Massot: [*LeanBlueprint*](https://github.com/PatrickMassot/leanblueprint/), A plasTeX plugin allowing to write blueprints for Lean 4 projects.


**The definitions and results to formalize**

The final LEAN4 code is most likely to be different from the following code snippets but at the very least it is good to know and verify that formalization is possible with the current technology stack; LEAN4 and the Mathlib library.

**Item name**

Definition 1.

**Formal statement**

**Definition 1**: Define a model of prime gaps as a Cayley Table *T*
constructed from a *Cummutative Partial Groupoid* (*J*, +) based on a
subset *J* of *Z* containing the infinite set of prime numbers and their
additive inverses, such that the elements of the first row of *T* are
the primes and the elements of the first column of *T* are their
additive inverses.

**Notes**

The set *J* is defined as follows *J* = (\...,−*p*<sub>n+2</sub>, −*p*<sub>n+1</sub>,
−*p*<sub>n</sub>, *p*<sub>n</sub>, p<sub>n+1</sub>, *p*<sub>n+2</sub>, \...). Notice that since primes are
infinite then by definition the structure T is also infinite. The structures used by LEAN4 in defining *T* must reflect
this property.

**LEAN4 code**
```
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Defs
import Mathlib.Tactic.Basic

open List Nat

-- Define the set of primes and their additive inverses
def primes_and_inverses : List ℤ :=
  (List.range 100).filter Nat.Prime |>.map (λ p => [↑p, -↑p]) |> List.join

-- Construct the Cayley table T for a finite portion
def cayley_table (n : ℕ) : List (List ℤ) :=
  let primes := (List.range n).filter Nat.Prime |>.map (λ p => ↑p)
  let inverses := primes.map (λ p => -p)
  let first_row := primes
  let first_column := inverses
  let table := first_column.map (λ inv => first_row.map (λ p => p + inv))
  first_row :: table

-- Example of using the cayley_table with a finite portion
def T : List (List ℤ) := cayley_table 30

#eval T -- To visualize a portion of the table
```

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------
**Item name**

Definition 2.

**Formal statement**

> **Definition 2**: Define a *v* x *w* sub-array *TT*<sub>i</sub> of *T* such that *v, w* ≥ 2.

**Notes**

Definition 2 defines a sub-array which is later used to algebraically
construct a pattern.

> Example: *TT*<sub>1</sub> = ((2, 4, 8, 10), (0, 2, 6, 8), (-2, 0, 4, 6), (-6, -4, 0, 2)).

**LEAN4 code**
```
-- Define a sub-array TTi of T, where v x w are its dimensions
def sub_array (T : List (List ℤ)) (r c v w : ℕ) : List (List ℤ) :=
  (T.drop r).take v |>.map (λ row => (row.drop c).take w)

-- Example: Extract a 3x3 sub-array from T
def TT1 : List (List ℤ) := sub_array T 1 1 3 3

#eval TT1 -- Visualize the sub-array
```

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Definition 3.

**Formal statement**

> **Definition 3**: Define a 4-tuple *β* = (*A, B, L, E*) such that the
> values of its elements are the vertices of *TT*<sub>i</sub>.

**Notes**

This is one of the structures used in the analysis of *T*.

> Example: for *TT*<sub>1</sub>, we have *TT*<sub>1</sub>.*β* = (2, 10, -6, 2).

**LEAN4 code**
```
-- Define the structure for the 4-tuple β
structure Beta where
  A : ℤ
  B : ℤ
  L : ℤ
  E : ℤ

-- Create a 4-tuple β from the vertices of a sub-array TTi
def create_beta (TTi : List (List ℤ)) : Beta :=
  ⟨TTi.head!.head!, TTi.head!.getLast!, TTi.getLast!.head!, TTi.getLast!.getLast!⟩

--- -- Provide a Repr instance for Beta to define how it should be displayed
--- instance : Repr Beta :=
---  ⟨fun β => s!"⟨{β.A}, {β.B}, {β.L}, {β.E}⟩"⟩

-- Example usage: Create β for TT1
def β1 : Beta := create_beta TT1

--- #eval β1 -- Visualize β1

#eval β1.A -- Visualize β1
#eval β1.B -- Visualize β1
#eval β1.L -- Visualize β1
#eval β1.E -- Visualize β1
```

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Lemma 4.1. This is the first Lemma.

**Formal statement**

> **Lemma 4.1** : Prove that: Given a 4-tuple *β* then *A* + *E* = *B* + *L*.

**Notes**

This is one of the results used in the subsequent proofs.

The proof is derived from the construction of *T*.

**LEAN4 code**
```
lemma lemma_4_1 (m n c k : ℤ) :
  let TTi_A := m + n
  let TTi_B := m + (n + k)
  let TTi_L := (m + c) + n
  let TTi_E := (m + c) + (n + k)
  TTi_B + TTi_L = TTi_A + TTi_E :=
by
  -- Expand and simplify the expressions
  linarith
```

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Lemma 4.2. This is the second Lemma.

**Formal statement**

> **Lema 4.2** : Prove that: All prime numbers greater than 3 can be expressed in the form 6*n* + 1 or 6*n* − 1.
>
> (A known result).

**Notes**

This result is used in the subsequent proofs.

**LEAN4 code**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Lemma 4.3. this is the third Lemma.

**Formal statement**

> **Lemma 4.3**: Let *t*<sub>m,n</sub> be a term in *T* where the indexes *m* and *n* are zero based and refer to the
> rows and columns in *T* respectively.

> Prove that:
>
> For every prime *p*<sub>α</sub> ≥ 5, there exists a sub-array *TT*<sub>i</sub> ∈ *T*
> such that the following properties are simultaneously true;
>
> Property 1 : *TT*<sub>i</sub>.*A* + 3 ∈ {6*n* ± 1\|*n* ∈ *N*<sub>1</sub>}
>
> Property 2 : (*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E* ∈ {6*n* ± 1\|*n* ∈
> *N*<sub>1</sub>}
>
> Property 3 : *TT*<sub>i</sub>.*L* ≡ 0 (mod 6)
>
> Property 4 : *TT*<sub>i</sub>.*A* = *TT*<sub>i</sub>.*E*
>
> Property 5 : *TT*<sub>i</sub>.*B* + 3 ∈ {6*n* ± 1\|*n* ∈ *N*<sub>1</sub>}
>
> If and only if
>
> for *TT*<sub>i</sub>.*A* + 3 ∈ {6*n* − 1\|*n* ∈ *N*<sub>1</sub>};
>
> *TT*<sub>i</sub>.*A* = 6*x* + 6*y* − 4
>
> *TT*<sub>i</sub>.*B* = 6*x* + 12*y* − 8
>
> *TT*<sub>i</sub>.*L* = 6*x*
>
> *TT*<sub>i</sub>.*E* = 6*x* + 6*y* − 4
>
> for *TT*<sub>i</sub>.*A* + 3 ∈ {6*n* + 1\|*n* ∈ *N*<sub>1</sub>};
>
> *TT*<sub>i</sub>.*A* = 6*x* + 6*y* − 2
>
> *TT*<sub>i</sub>.*B* = 6*x* + 12*y* − 4
>
> *TT*<sub>i</sub>.*L* = 6*x*
>
> *TT*<sub>i</sub>.*E* = 6*x* + 6*y* − 2
>
> where *n* ∈ *N*<sub>1</sub>, *x* \< *n*, *y* \> 0, *n* = *x* + *y*,
> (*TT*<sub>i</sub>.*A* + 3) = *p*<sub>α</sub> and *TT*<sub>i</sub>.*A* = *t*<sub>2,k</sub>.

**Notes**

This result demonstrates the existence of a pattern. It algebraically
shows that for every prime *p*<sub>α</sub> ≥ 5, there is a pattern *TT*<sub>i</sub> that
defines a pair of integers *Q*<sub>i</sub> and *R*<sub>i</sub> such that *R*<sub>i</sub> − *Q*<sub>i</sub> =
*p*<sub>α</sub> − 3.

The key in the proof of this result is the following analysis:

-   We are given *p*<sub>α</sub> as a constant quantity.

-   Now *p*<sub>α</sub> can be expressed in the form 6*n* ± 1.

-   This implies that *n* in the expression 6*n* ± 1 is constant.

-   We then let *n* = *x* + *y*.

-   We then use combinatory analysis to heuristically determine which
    expressions to assign to *A*, *B*, *L* and *E* from the sets *M* =
    (6*x*, 6*y*, -4, 6*x*, 6*y*, -4) and *N* = (6*x*, 6*y*, -2, 6*x*,
    6*y*, -2) such that the five (5) properties of Lemma 4.3 are
    satisfied.

But how are the sets *M* and *N* derived?

Notice that by Lemma 4.3, *TT*<sub>i</sub>.*A* = *TT*<sub>i</sub>.*E* and (*TT*<sub>i</sub>.*A* +
3) = *p*<sub>α</sub>. Since *p*<sub>α</sub> is prime then it can be expressed in the forms
6*n* ± 1 or 6(*x* + *y*) ± 1. And by Lemma 4.1, *A* + E = *B* + *L*,
which implies that *TT*<sub>i</sub>.*B* + *TT*<sub>i</sub>.*L* = *TT*<sub>i</sub>.*A* + *TT*<sub>i</sub>.E =
((6*x +* 6*y* + -4) + (6*x +* 6*y +* -4)) or ((6*x +* 6*y +* -2) + (6*x
+* 6*y +* -2)) depending on which form *p*<sub>α</sub> can be expressed.

**LEAN4 code**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Lemma 4.4. This is the fourth Lemma.

**Formal statement**

> **Lemma 4.4**: Let any sub-array *TT*<sub>i</sub> that satisfies Lemma 4.3 be referred to as a *Prime Array*.

> Prove that: For every prime *p*<sub>α</sub> ≥ 5, there are infinitely many
> *Prime Arrays* such that *TT<sub>i</sub>.A = p*<sub>α</sub> *− 3.*

**Notes**

This will show that for any prime *p*<sub>α</sub> ≥ 5 the pattern defined by the
*Prime Array TT*<sub>i</sub> occurs infinitely often and that consequently, the
integer pairs (*Q*<sub>i</sub>, *R*<sub>i</sub>) also occur infinitely often.

The key in the proof is to show that for any prime *p*<sub>α</sub> ≥ 5,

-   *p*<sub>α</sub> is constant.

-   Which implies *n* is constant.

-   But *n* = *x* + *y*

-   Now changing the value of *y* changes the value of *x in order* to
    maintain the equality *n* = *x* + *y*.

-   Changing the value of *x* changes the value of *L* since *L* = 6*x*.

-   Changing the value of *L* changes the value of *B* since *B* + *L* =
    *A* + *E* and *A* + *E* is a constant expression.

-   This implies that the value of *y* can be changed infinitely often
    and each change represents a different sub-array or *Prime Array*
    *TT*<sub>i</sub>.

**LEAN4 code**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Lemma 4.5. This is the fifth Lemma.

**Formal statement**

> **Lemma 4.5**: Prove that: For every prime *p*<sub>α</sub> ≥ 5, there exists infinitely many *Prime Arrays*,
> *TT*<sub>i</sub>, such that *TT*<sub>i</sub>.*A* = *p*<sub>α</sub> − 3 and (*T*<sub>i</sub>.*B* + 3) and ((*T*<sub>i</sub>.
> *B* + 3) −*T*<sub>i</sub>.*E*) are prime.

**Notes**

This will show that for any prime *p*<sub>α</sub> ≥ 5, the *Prime Arrays* *TT*<sub>i</sub>
occur infinitely often and *Q*<sub>i</sub> and *R*<sub>i</sub> are prime. Notice that
here, (*TT*<sub>i</sub>.*B* + 3) = *R*<sub>i</sub> and *Q*<sub>i</sub> = ((*TT*<sub>i</sub>.*B* + 3) −
*TT*<sub>i</sub>.*E*).

The proof here relies on the construction of *T* where all the elements
on the first row of *T* are prime

We can then algebraically show that (*TT*<sub>i</sub>.*B* + 3) and
((*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E*) are prime.

**LEAN4 code**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Theorem 1. The first Theorem, the first of the two main results.

**Formal statement**

**Theorem 1**: Prove that: For every prime *p*<sub>α</sub>, there exists
infinitely many pairs of primes, (*p*<sub>n</sub>, *p*<sub>n+m</sub>), such that (*p*<sub>n+m</sub>
− *p*<sub>n</sub>) = *p*<sub>α</sub> − 3, where n, α ≥ 3, m ≥ 1, and *p*<sub>n</sub> is the n<sup>th</sup>
prime.

**Notes**

The claim is that this result is implied from the previous results as
demonstrated in the following steps:

**Step 1**: By Lemma 4.5, and the construction of *T*, *TT*<sub>i</sub>.*A* and
*TT*<sub>i</sub>.*E* are prime gaps.

**Step 2**: By Lemma 4.3, *TT*<sub>i</sub>.*A* = *TT*<sub>i</sub>*.E*.

This is equivalent to: (*TT*<sub>i</sub>.*A* + 3) − 3 = ((*TT*<sub>i</sub>.*B* + 3) −
((*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E*)).

**Step 3**: By Lemma 4.5, the following are prime; (*TT*<sub>i</sub>.*A* + 3),
((*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E*), (*TT*<sub>i</sub>.*B* + 3).

**Step 4**: By Lemma 4.5, for every prime (*TT*<sub>i</sub>.*A* + 3) ≥ 5, there
are infinitely many of the following pairs of primes defined as:
(((*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E*), (*TT*<sub>i</sub>.*B* + 3)).

We can then see that the following statement is implied:

> For every prime (*TT*<sub>i</sub>.*A* + 3) ≥ 5, there exists infinitely many
> pairs of primes, (((*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E*), (*TT*<sub>i</sub>.*B* +
> 3)), such that ((*TT*<sub>i</sub>.*B* + 3) − ((*TT*<sub>i</sub>.*B* + 3) − *TT*<sub>i</sub>.*E*))
> = (*TT*<sub>i</sub>.*A* + 3) − 3.

This statement is equivalent to the formal statement of Theorem 1 which
can be is re-stated using the following equivalent assignments:

> *p*<sub>α</sub> − 3 = *TT*<sub>i</sub>.*A*.
>
> *p*<sub>n+m</sub> − 3 = *TT*<sub>i</sub>.*B.*
>
> *p*<sub>α</sub> − *p*<sub>n</sub> = *TT*<sub>i</sub>.*L*.
>
> *p*<sub>n+m</sub> − *p*<sub>n</sub> = *TT*<sub>i</sub>.*E.*

**LEAN4 code**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Item name**

Theorem 2. This is the second Theorem, the second of the two main
results.

**Formal statement**

> **Theorem 2**: Prove that there exist infinitely many pairs of primes with a gap of 2.

**Notes**

This result is just a special case of Theorem 1 when *p*<sub>α</sub> is set to 5.
I am sure this would be resolved by LEAN4 using the \"refl\" similar
tactic.

**LEAN4 code**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**LEAN4 code annotation**

  -----------------------------------------------------------------------

  -----------------------------------------------------------------------

**Outcome and Conclusion**

By formalizing the results presented in the paper [*Structure in Prime
Gaps*](https://www.researchsquare.com/article/rs-4058806/latest), we
hope to contribute to the body of knowledge in mathematics as well as
help establish the use of proof assistants like LEAN in academia,
research and industry in general.

![]({{ site.repository_url }}?raw=true/vertopal_bfea56392a264e1da44fa95b98b2549d/media/image1.png)
