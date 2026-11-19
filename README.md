# An asymptotic formula for the equality count in Erdős Problem 878(iv)

Let $E(x)$ count positive integers $n<x$ for which $f(n)=F(n)$, with the definitions in Formal Conjectures. Set

```math
Y=\exp((\log x)^{2/3}),\qquad K=\lfloor (\log x)^{1/20}\rfloor,\qquad L=\lfloor\log_2 x\rfloor .
```

For each positive integer $m<x/Y$ with at most $K$ distinct prime factors, let $I_m(x)$ be the set of $u$ in $(\max(Y,P^+(m)),x/m)$ passing the following finite test. Here $P^+(1)=0$. Use the prime factors of $m$ and the variable $u$ as bases. Each product with exponents from $0$ to $L$ and value in $[2,mu]$ must be at most the sum of the largest pure powers at most $mu$ of its bases with positive exponent. Use the same exponent range for the pure powers.

The theorem proves

```math
E(x)\sim
\sum_{\substack{1\le m<x/Y\\ \omega(m)\le K}}
\int_{I_m(x)}\frac{du}{\log u}.
```

The proof bounds the count discarded as smooth, divisible by a large square, or having too many prime factors by $o(x/\log x)$. Each retained integer has a unique largest prime $p$, and the finite test at $u=p$ characterizes equality for $n=mp$. Polynomial roots divide the real test into finitely many intervals. Their number grows slowly enough to sum the quantitative prime number theorem errors over all intervals and cofactors. The primes alone give $E(x)\gg x/\log x$, which turns the additive error into an asymptotic equivalent.

The statement is in `Challenge.lean`. The proof is `Erdos878.erdos_878.parts.iv` in `Solution.lean`. With Lean 4.35.0, run `lake exe cache get` followed by `lake build`. The Comparator challenge contains the statement as a placeholder. The solution uses only `propext`, `Classical.choice`, and `Quot.sound`.

Rivka Lipkovitz directed the investigation and maintains the formalization. OpenAI Codex developed the argument and Lean code. The source is licensed under Apache-2.0. See [Erdős Problem 878](https://www.erdosproblems.com/878) and the [existing Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/878.lean).
