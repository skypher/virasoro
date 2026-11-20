# S2: Pole Orders, Top Jantzen Layer Formula, and Unconditional Sharpness for Sphere Blocks

## 1. Setup and Conventions

Let $p, p' \geq 2$ be coprime integers. By the $b \leftrightarrow b^{-1}$ symmetry of $c(b) = 1 + 6(b + b^{-1})^2$, assume without loss of generality that $p' > p \geq 2$, and set
\[
b_\star = i\sqrt{\frac{p'}{p}}, \qquad c_\star = c(b_\star) = 1 - \frac{6(p' - p)^2}{pp'}, \qquad Q_\star = b_\star + b_\star^{-1} = i\frac{p' - p}{\sqrt{pp'}}.
\]
Let $\lambda = h_{r, s}(b_\star) = \frac{(p'r - ps)^2 - (p' - p)^2}{4pp'}$ be an interior Kac weight ($1 \leq r \leq p - 1$, $1 \leq s \leq p' - 1$). Replacing $(r, s)$ by $(p - r, p' - s)$ if necessary, assume $n_1 := p'r + ps < pp'$ (equality is impossible since $\gcd(p, p') = 1$ and $0 < r < p$). Set $n_0 := p'r - ps \neq 0$.

Following torus `paper.tex` Theorem 5.8, define the Jantzen singular-vector levels for $k \geq 1$:
\begin{align*}
\ell^+_{2j+1} &= (r + jp)(s + jp'), & \ell^-_{2j+1} &= ((j+1)p - r)((j+1)p' - s) \qquad (j \geq 0), \\
\ell^+_{2j} &= j(j pp' + n_0), & \ell^-_{2j} &= j(j pp' - n_0) \qquad (j \geq 1),
\end{align*}
with $\ell_k := \min(\ell^+_k, \ell^-_k)$, $\mu^\pm_k := \lambda + \ell^\pm_k$, and Jantzen depth
\[
j_N(\lambda) := \max\bigl(\{0\} \cup \{k \geq 1 : \ell_k \leq N\}\bigr).
\]
For every $k \geq 1$, the shifted weights $\mu^\pm_k$ have positive integer Coulomb momenta $m^\pm_k > 0$ (where $\mu^\pm_k = \frac{(m^\pm_k)^2 - (p'-p)^2}{4pp'}$) given by:
- for odd $k = 2j + 1$: $m^+_{2j+1} = 2j pp' + n_1 < 2(j+1)pp' - n_1 = m^-_{2j+1}$,
- for even $k = 2j$: $m^+_{2j} = 2j pp' + n_0$ and $m^-_{2j} = 2j pp' - n_0$ (distinct since $n_0 \neq 0$).

In both parities, $m^+_k \neq m^-_k$ and $m^+_k + m^-_k = 2k pp'$. Denote the smaller and larger momenta by $m^{\mathrm{small}}_k < m^{\mathrm{big}}_k$ (with corresponding levels $\ell^{\mathrm{small}}_k < \ell^{\mathrm{big}}_k$, shifted weights $\mu^{\mathrm{small}}_k < \mu^{\mathrm{big}}_k$, and singular vectors $w^{\mathrm{small}}_k, w^{\mathrm{big}}_k$). Note that $m^{\mathrm{big}}_k \geq k pp' + 1$ for every $k \geq 1$ (since $n_1 < pp'$ and $n_0 \neq 0$).

---

## 2. Pole-Order Upper Bound and Top Jantzen Layer Formula (`S2_TOP`)

**Theorem S2A (Jantzen pole-order bound).** *For every coprime $p, p' \geq 2$, every interior Kac weight $\lambda = h_{r,s}(b_\star)$, and every level $N \geq 0$, both $\mathcal{B}_N(c_\star, \Delta, \Delta_i)$ and $H_N(c_\star, \Delta, \Delta_i)$ have poles of order at most $j_N(\lambda)$ at $\Delta = \lambda$.*

**Proof.** By torus `paper.tex` Theorem 5.8 (Iohara–Koga 2011, Thm. 6.3 and Prop. 5.4; Astashkevich 1997, Thm. B(e)), the inverse Shapovalov matrix $G_N(c_\star, \Delta)^{-1}$ has a pole of order exactly $j_N(\lambda)$ at $\Delta = \lambda$. Since $\gamma_Y(\Delta; \Delta_a, \Delta_b)$ is polynomial in $\Delta$, $\mathcal{B}_N = \gamma^{(4,3)}(\Delta)^T G_N(c_\star, \Delta)^{-1} \gamma^{(1,2)}(\Delta)$ has a pole of order at most $j_N(\lambda)$ at $\Delta = \lambda$. Since $H(c_\star, \Delta, \Delta_i; q) = \widetilde\Phi(c_\star, \Delta, \Delta_i; z(q))^{-1} \sum_{m=0}^\infty \mathcal{B}_m(c_\star, \Delta, \Delta_i) z(q)^m$ where $\widetilde\Phi^{-1}$ has coefficients polynomial in $\Delta$ and $j_m(\lambda) \leq j_N(\lambda)$ for $m \leq N$, $H_N(c_\star, \Delta, \Delta_i)$ also has a pole of order at most $j_N(\lambda)$ at $\Delta = \lambda$. $\square$

**Lemma S2.1 (Explicit singular three-point polynomials $\pi^\pm_k$).** Let $w^\pm_k \in M(c_\star, \lambda)_{\ell^\pm_k}$ ($k \geq 1$) be the unique singular vector with $L_{-1}^{\ell^\pm_k}$-coefficient equal to $1$, and set $\pi^\pm_k(\Delta_a, \Delta_b) := \langle w^\pm_k | \Phi_b(1) | \Delta_a \rangle$. Then:
1. For odd $k = 2j + 1$ ($j \geq 0$), setting $(R^+_k, S^+_k) = (r + jp, s + jp')$ and $(R^-_k, S^-_k) = ((j+1)p - r, (j+1)p' - s)$,
   \[
   \pi^\pm_k(\Delta_a, \Delta_b) = P_{R^\pm_k, S^\pm_k}(b_\star, \Delta_a, \Delta_b).
   \]
2. For even $k = 2j$ ($j \geq 1$), setting $(R^+_k, S^+_k) = (r + jp, jp' - s)$ and $(R^-_k, S^-_k) = (jp - r, jp' + s)$,
   \[
   \pi^\pm_k(\Delta_a, \Delta_b) = P_{r, s}(b_\star, \Delta_a, \Delta_b)\, P_{R^\pm_k, S^\pm_k}(b_\star, \Delta_a, \Delta_b).
   \]
3. Parameterizing $\Lambda_a = i a_a/\sqrt{pp'}$, $\Lambda_b = i a_b/\sqrt{pp'}$ ($\Delta_a = \frac{a_a^2 - (p'-p)^2}{4pp'}$), every root of $\pi^\pm_k(\Delta_a, \Delta_b)$ has $|a_a \pm a_b| \leq m^\pm_k - p' - p$, and $a_a - a_b = m^\pm_k - p' - p$ is a root of $\pi^\pm_k(\Delta_a, \Delta_b)$.

**Proof.**
By torus `paper.tex` Lemma 6.6, for every positive pair $(R, S)$ the normalized singular vector $\chi_{R, S}(b)$ is regular at $b_\star$ with $L_{-1}^{RS}$-coefficient $1$, and satisfies $\langle \chi_{R, S}(b_\star) | \Phi_b(1) | \Delta_a \rangle = P_{R, S}(b_\star, \Delta_a, \Delta_b)$ by Proposition 3 of `s1_confluence.md`.
- For odd $k = 2j + 1$, $h_{R^\pm_k, S^\pm_k}(b_\star) = \lambda$ and $R^\pm_k S^\pm_k = \ell^\pm_k$. Since the singular space at weight $\lambda + \ell^\pm_k$ in $M(c_\star, \lambda)$ is $1$-dimensional (Iohara–Koga 2011, Prop. 5.4), $w^\pm_k = \chi_{R^\pm_k, S^\pm_k}(b_\star)$, giving (1).
- For even $k = 2j$ ($j \geq 1$), $R^\pm_k, S^\pm_k \geq 1$, $h_{R^\pm_k, S^\pm_k}(b_\star) = \mu^+_1 = \lambda + rs$, and $R^\pm_k S^\pm_k = \ell^\pm_k - rs$. Pushing $\chi_{R^\pm_k, S^\pm_k}(b_\star) \in M(c_\star, \mu^+_1)$ forward along the injective Verma embedding $j_{w^+_1} : M(c_\star, \mu^+_1) \hookrightarrow M(c_\star, \lambda)$ ($v_{\mu^+_1} \mapsto \chi_{r, s}(b_\star)$) gives a singular vector of level $\ell^\pm_k$ with $L_{-1}^{\ell^\pm_k}$-coefficient $1$, hence $w^\pm_k = j_{w^+_1}(\chi_{R^\pm_k, S^\pm_k}(b_\star))$. Applying three-point factorization (Lemma 2 of `s1_confluence.md`) yields (2).
- For (3): with $b_\star = i p'/\sqrt{pp'}$ and $b_\star^{-1} = -i p/\sqrt{pp'}$, the factors of $P_{R, S}(b_\star, \Delta_a, \Delta_b)$ vanish precisely when $a_a \pm a_b = -(j p' - l p)$ for $j \in \{-(R-1), -(R-3), \dots, R-1\}$ and $l \in \{-(S-1), -(S-3), \dots, S-1\}$. The maximum value of $|j p' - l p|$ is $(R - 1)p' + (S - 1)p = R p' + S p - p' - p$, attained at $(j, l) = (-(R-1), S-1)$. For both parities of $k$, $R^\pm_k p' + S^\pm_k p = m^\pm_k$, and for even $k$ the additional factor $P_{r,s}$ has maximum $(r - 1)p' + (s - 1)p = n_1 - p' - p < pp' - p' - p < m^\pm_k - p' - p$. $\square$

**Theorem S2B (Top Jantzen layer formula for $\mathcal{B}_N$ and $H_N$).** *Let $k \geq 1$ and $\ell_k \leq N < \ell_{k+1}$. Put $\gamma^\pm_k := B^k(w^\pm_k, w^\pm_k)$ (the exact same Jantzen layer norms as in torus `paper.tex` Theorem 5.9). Then $j_N(\lambda) = k$; for each sign with $\ell^\pm_k \leq N$, we have $\gamma^\pm_k \neq 0$ and $\det G_M(c_\star, \mu^\pm_k) \neq 0$ for all $0 \leq M \leq N - \ell^\pm_k$; and as rational functions of $(\Delta_1, \Delta_2, \Delta_3, \Delta_4)$:*
\begin{align*}
\lim_{\Delta \to \lambda} (\Delta - \lambda)^k \mathcal{B}_N(c_\star, \Delta, \Delta_i)
&= \sum_{\pm:\; \ell^\pm_k \leq N} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_1, \Delta_2)}{\gamma^\pm_k}\, \mathcal{B}_{N - \ell^\pm_k}(c_\star, \mu^\pm_k, \Delta_i), \\
\lim_{\Delta \to \lambda} (\Delta - \lambda)^k H_N(c_\star, \Delta, \Delta_i)
&= \sum_{\pm:\; \ell^\pm_k \leq N} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_1, \Delta_2)}{\gamma^\pm_k}\, H_{N - \ell^\pm_k}(c_\star, \mu^\pm_k, \Delta_i).
\end{align*}

**Proof.**
By the proof of torus `paper.tex` Theorem 5.9, for every $N'$ with $\ell_k \leq N' \leq N$, $k$ is the maximal local Smith exponent of $G_{N'}(c_\star, \lambda + x)$, $J^k_{N'}(c_\star, \lambda) = \bigoplus_{\pm: \ell^\pm_k \leq N'} (W^\pm_k)_{N'}$ is a $B^k$-orthogonal direct sum with $B^k(L_{-Z} w^\pm_k, L_{-Z'} w^\pm_k) = \gamma^\pm_k G_{N' - \ell^\pm_k}(c_\star, \mu^\pm_k)_{Z, Z'}$, $\gamma^\pm_k \neq 0$, and $\det G_M(c_\star, \mu^\pm_k) \neq 0$ for all $M \leq N - \ell^\pm_k$. Applying torus `paper.tex` Lemma 5.4(ii) to the bilinear pairing $\mathcal{B}_{N'} = \gamma^{(4,3)}(\Delta)^T G_{N'}(c_\star, \Delta)^{-1} \gamma^{(1,2)}(\Delta)$ together with three-point factorization (Lemma 2 of `s1_confluence.md`) gives
\[
[x^{-k}] \mathcal{B}_{N'}(c_\star, \lambda + x, \Delta_i)
= \sum_{\pm:\; \ell^\pm_k \leq N'} \frac{1}{\gamma^\pm_k} \sum_{|Z|=|Z'|=N'-\ell^\pm_k} \langle L_{-Z} w^\pm_k | \Phi_3(1) | \Delta_4 \rangle \bigl(G_{N'-\ell^\pm_k}(c_\star, \mu^\pm_k)^{-1}\bigr)_{Z, Z'} \langle L_{-Z'} w^\pm_k | \Phi_2(1) | \Delta_1 \rangle
\]
\[
= \sum_{\pm:\; \ell^\pm_k \leq N'} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_1, \Delta_2)}{\gamma^\pm_k}\, \mathcal{B}_{N' - \ell^\pm_k}(c_\star, \mu^\pm_k, \Delta_i).
\]
This proves the formula for $\mathcal{B}_N$.

For $H_N$, write $H(c_\star, \Delta, \Delta_i; q) = \widetilde\Phi(c_\star, \Delta, \Delta_i; z(q))^{-1} \sum_{m=0}^\infty \mathcal{B}_m(c_\star, \Delta, \Delta_i) z(q)^m$, where $\widetilde\Phi(c_\star, \Delta, \Delta_i; z) = (16q/z)^{\Delta - \frac{c_\star-1}{24}} (1-z)^{\frac{c_\star-1}{24} - \Delta_2 - \Delta_3} \theta_3(q)^{\frac{c_\star-1}{2} - 4(\Delta_1+\Delta_2+\Delta_3+\Delta_4)}$. Since $\widetilde\Phi(c_\star, \lambda + x, \Delta_i; z(q))^{-1} = \widetilde\Phi(c_\star, \lambda, \Delta_i; z(q))^{-1} + O(x)$ is regular at $x = 0$ and $\mathcal{B}_m$ has pole order $< k$ for $m < \ell_k$, taking $[x^{-k}]$ modulo $q^{\ell_{k+1}}$ yields
\begin{align*}
\sum_{N=\ell_k}^{\ell_{k+1}-1} [x^{-k}] H_N(c_\star, \lambda + x, \Delta_i)\, (16 q)^N
&\equiv \widetilde\Phi(c_\star, \lambda, \Delta_i; z(q))^{-1} \sum_{m=\ell_k}^{\ell_{k+1}-1} [x^{-k}] \mathcal{B}_m(c_\star, \lambda + x, \Delta_i)\, z(q)^m \\
&\equiv \sum_{\pm} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_1, \Delta_2)}{\gamma^\pm_k}\, \widetilde\Phi(c_\star, \lambda, \Delta_i; z(q))^{-1} z(q)^{\ell^\pm_k} \sum_{r=0}^{\ell_{k+1}-1-\ell^\pm_k} \mathcal{B}_r(c_\star, \mu^\pm_k, \Delta_i)\, z(q)^r \\
&\equiv \sum_{\pm} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_1, \Delta_2)}{\gamma^\pm_k}\, (16 q)^{\ell^\pm_k} \sum_{r=0}^{\ell_{k+1}-1-\ell^\pm_k} H_r(c_\star, \mu^\pm_k, \Delta_i)\, (16 q)^r \pmod{q^{\ell_{k+1}}},
\end{align*}
using $\widetilde\Phi(c_\star, \lambda, \Delta_i; z(q))^{-1} z(q)^{\ell^\pm_k} = (16 q)^{\ell^\pm_k} \widetilde\Phi(c_\star, \mu^\pm_k, \Delta_i; z(q))^{-1}$. Extracting the coefficient of $(16 q)^N$ yields the top-layer formula for $H_N$. $\square$

---

## 3. Unconditional Sharpness for $\mathcal{B}_N$ and $H_N$ (`S2_SHARP`)

**Theorem S2C (Unconditional sharpness for $\mathcal{B}_N$).** *For every coprime pair $p, p' \geq 2$, every interior Kac weight $\lambda = h_{r, s}(b_\star)$, and every level $N \geq 1$, the sphere block coefficient $\mathcal{B}_N(c_\star, \Delta, \Delta_1, \Delta_2, \Delta_3, \Delta_4)$ (for indeterminate external weights) has a pole of order **exactly** $j_N(\lambda)$ at $\Delta = \lambda$.*

**Proof.**
Set $k = j_N(\lambda)$. If $k = 0$, the claim is trivial; assume $k \geq 1$, so $\ell_k \leq N < \ell_{k+1}$. Write $M := N - \ell^{\mathrm{small}}_k \geq 0$ and $\mu := \mu^{\mathrm{small}}_k$. By Theorem S2B, $\det G_m(c_\star, \mu) \neq 0$ for all $0 \leq m \leq M$, and it suffices to exhibit one specialization $(\Delta_1, \Delta_2, \Delta_3, \Delta_4)$ at which:
(a) $\pi^{\mathrm{big}}_k(\Delta_4, \Delta_3) = 0$ (if $\ell^{\mathrm{big}}_k \leq N$),
(b) $\pi^{\mathrm{small}}_k(\Delta_4, \Delta_3) \neq 0$ and $\pi^{\mathrm{small}}_k(\Delta_1, \Delta_2) \neq 0$, and
(c) $\mathcal{B}_M(c_\star, \mu, \Delta_1, \Delta_2, \Delta_3, \Delta_4) \neq 0$.

Choose the single rational specialization $\Lambda_j = i \tilde a_j / \sqrt{pp'}$ ($\Delta_j = \frac{\tilde a_j^2 - (p'-p)^2}{4pp'} \in \mathbb{Q}$) given by:
- $\tilde a_2 = 2p' - p$ (so $\Delta_2 = h_{2, 1}(b_\star)$),
- $\tilde a_1 = m^{\mathrm{small}}_k + p'$ (so $\Lambda_1 = \Lambda_\mu + b_\star$, where $\Lambda_\mu = i m^{\mathrm{small}}_k / \sqrt{pp'}$),
- $\tilde a_3 = -(k pp' - p)$ and $\tilde a_4 = -\frac{m^{\mathrm{small}}_k - m^{\mathrm{big}}_k + 2p'}{2}$ (putting $a_3 = -\tilde a_3$ and $a_4 = -\tilde a_4$, so $a_3 - a_4 = m^{\mathrm{big}}_k - p' - p$ and $a_3 + a_4 = m^{\mathrm{small}}_k + p' - p$).

We verify (a), (b), (c):
- **(a)** Since $a_4 - a_3 = -(m^{\mathrm{big}}_k - p' - p)$, Lemma S2.1(3) gives $\pi^{\mathrm{big}}_k(\Delta_4, \Delta_3) = 0$.
- **(b)** All four positive quantities satisfy strict inequalities above the maximal root bound $m^{\mathrm{small}}_k - p' - p$ of $\pi^{\mathrm{small}}_k$ (Lemma S2.1(3)):
  \begin{align*}
  \tilde a_1 + \tilde a_2 &= m^{\mathrm{small}}_k + 3p' - p > m^{\mathrm{small}}_k - p' - p, &
  \tilde a_1 - \tilde a_2 &= m^{\mathrm{small}}_k - p' + p > m^{\mathrm{small}}_k - p' - p, \\
  a_3 - a_4 &= m^{\mathrm{big}}_k - p' - p > m^{\mathrm{small}}_k - p' - p, &
  a_3 + a_4 &= m^{\mathrm{small}}_k + p' - p > m^{\mathrm{small}}_k - p' - p.
  \end{align*}
  Hence $\pi^{\mathrm{small}}_k(\Delta_1, \Delta_2) \neq 0$ and $\pi^{\mathrm{small}}_k(\Delta_4, \Delta_3) \neq 0$.
- **(c)** For generic $(b, \Lambda_\mu, \Lambda_3, \Lambda_4)$ with $\Delta_2 = h_{2,1}(b)$ and $\Lambda_1 = \Lambda_\mu + b$, the level-$2$ BPZ null vector $(L_{-2} + b^{-2} L_{-1}^2)|h_{2,1}\rangle$ has vanishing three-point coupling with $(\Delta_1, \mu)$, so $\mathcal{F}(z) = z^{\mu - \Delta_1 - \Delta_2}\mathcal{B}(z)$ satisfies the second-order BPZ differential equation
  \[
  \left(b^{-2}\partial_z^2 - \left(\frac{1}{z} + \frac{1}{z-1}\right)\partial_z + \frac{\Delta_1}{z^2} + \frac{\Delta_3}{(z-1)^2} + \frac{\Delta_1 + \Delta_2 + \Delta_3 - \Delta_4}{z(1-z)}\right)\mathcal{F}(z) = 0,
  \]
  whose unique normalized power-series solution is $\mathcal{B}(z) = (1 - z)^\kappa \, {}_2F_1(A, B; C; z)$ with
  \[
  C = 1 + b^2 + b\Lambda_\mu, \quad \kappa = \frac{1 + b^2 + b\Lambda_3}{2}, \quad A = \frac{1 + b^2 + b(\Lambda_\mu + \Lambda_3 - \Lambda_4)}{2}, \quad B = \frac{1 + b^2 + b(\Lambda_\mu + \Lambda_3 + \Lambda_4)}{2}.
  \]
  Thus $\mathcal{B}_m = [z^m]((1 - z)^\kappa {}_2F_1(A, B; C; z))$ holds as an identity of rational functions of $(b, \Lambda_\mu, \Lambda_3, \Lambda_4)$ for every $m \geq 0$. At our specialization ($b_\star^2 = -p'/p$, $b_\star \Lambda_\mu = -m^{\mathrm{small}}_k/p$, $b_\star \Lambda_3 = a_3/p$, $b_\star \Lambda_4 = a_4/p$):
  1. $C = 1 - \frac{p' + m^{\mathrm{small}}_k}{p} \notin \{0, -1, \dots, -(M - 1)\}$: if $C = 1 - u$ for an integer $1 \leq u \leq M$, then $m^{\mathrm{small}}_k = u p - p'$, so $\Lambda_\mu = -(b_\star + u b_\star^{-1})$ and $\mu = h_{1, u}(b_\star)$, forcing $\det G_M(c_\star, \mu) = 0$ and contradicting Theorem S2B. Thus $(C)_M \neq 0$, so both sides of the rational identity for $\mathcal{B}_M$ are regular at this specialization.
  2. $B = \frac{1}{2}\bigl(1 - \frac{p' + m^{\mathrm{small}}_k}{p} + \frac{m^{\mathrm{small}}_k + p' - p}{p}\bigr) = 0$, so ${}_2F_1(A, 0; C; z) = 1$.
  3. $\kappa = \frac{1}{2}\bigl(1 - \frac{p'}{p} + \frac{k pp' - p}{p}\bigr) = \frac{(k p - 1) p'}{2 p}$. Since $\gcd(p, (kp - 1)p') = \gcd(p, -p') = 1$ and $p \geq 2$, $\kappa \notin \mathbb{Z}$.
  Therefore $\mathcal{B}_M = (-1)^M \binom{\kappa}{M} \neq 0$. $\square$

---

**Theorem S2D (Unconditional sharpness for $H_N$).** *For every coprime pair $p, p' \geq 2$, every interior Kac weight $\lambda = h_{r, s}(b_\star)$, and every level $N \geq 1$, the elliptic sphere coefficient $H_N(c_\star, \Delta, \Delta_1, \Delta_2, \Delta_3, \Delta_4)$ (for indeterminate external weights) has a pole of order **exactly** $j_N(\lambda)$ at $\Delta = \lambda$.*

**Proof.**
Fix $k = j_N(\lambda) \geq 1$, $M := N - \ell^{\mathrm{small}}_k \geq 0$, and $\mu := \mu^{\mathrm{small}}_k$. By Theorem S2B, $\det G_m(c_\star, \mu) \neq 0$ for all $0 \leq m \leq M$.

Specialize $(\Delta_1, \Delta_2) := (\mu, 0)$ (so $a_1 = m^{\mathrm{small}}_k$, $a_2 = p' - p$), and restrict $(\Delta_3, \Delta_4)$ to the affine line $\Lambda_3 - \Lambda_4 = i\alpha$, $\Lambda_3 + \Lambda_4 = i v$ ($v$ indeterminate), where
\[
X := m^{\mathrm{big}}_k - p' - p, \qquad \alpha := \frac{X}{\sqrt{pp'}}.
\]
We verify all four conditions on this line:
1. **Kills the big branch:** Since $\Lambda_3 - \Lambda_4 = i X / \sqrt{pp'}$, Lemma S2.1(3) gives $\pi^{\mathrm{big}}_k(\Delta_4, \Delta_3) \equiv 0$ identically in $v$.
2. **Nonvanishing on the small branch:**
   - For $(\Delta_1, \Delta_2) = (\mu, 0)$, both $a_1 + a_2 = m^{\mathrm{small}}_k + p' - p$ and $a_1 - a_2 = m^{\mathrm{small}}_k - p' + p$ strictly exceed $m^{\mathrm{small}}_k - p' - p$, so $\pi^{\mathrm{small}}_k(\mu, 0) \neq 0$ by Lemma S2.1(3).
   - For $(\Delta_4, \Delta_3)$ as a polynomial in $v$, $\pi^{\mathrm{small}}_k(\Delta_4, \Delta_3)$ is a product of factors $(v \pm \text{const})$ and $(\alpha \pm \text{const})$, where every $|\text{const}| \leq (m^{\mathrm{small}}_k - p' - p)/\sqrt{pp'} < \alpha$; hence none of the constant factors vanish, so $\pi^{\mathrm{small}}_k(\Delta_4, \Delta_3) \not\equiv 0$ as a polynomial in $v$.
3. **Exact collapse of $\mathcal{B}_m$ and closed form of $[v^M] H_M(v)$:**
   At $(\Delta_1, \Delta_2) = (\mu, 0)$, for every nonempty partition $Z = (z_1, \dots, z_r)$ the last factor of $\gamma_Z(\mu; \mu, 0)$ is $\mu + 0 + z_r \cdot 0 - \mu = 0$. Since $\det G_m(c_\star, \mu) \neq 0$ for all $0 \leq m \leq M$, we have $\mathcal{B}_m(c_\star, \mu, \mu, 0, \Delta_3(v), \Delta_4(v)) = \delta_{m, 0}$ for all $0 \leq m \leq M$. Therefore, modulo $q^{M+1}$,
   \[
   H(c_\star, \mu, \mu, 0, \Delta_3(v), \Delta_4(v); q)
   \equiv \left(\frac{16q}{z(q)}\right)^{\frac{c_\star-1}{24} - \mu} (1 - z(q))^{\Delta_3(v) - \frac{c_\star-1}{24}} \theta_3(q)^{4(\mu + \Delta_3(v) + \Delta_4(v)) - \frac{c_\star-1}{2}} \pmod{q^{M+1}}.
   \]
   Since $\Delta_3(v) = \frac{Q_\star^2}{4} + \frac{(v+\alpha)^2}{16}$, $\Delta_4(v) = \frac{Q_\star^2}{4} + \frac{(v-\alpha)^2}{16}$, and $1 - z = (\theta_4/\theta_3)^4$, the $v$-dependent factor is
   \[
   \bigl(\theta_3(q)\theta_4(q)\bigr)^{v^2/4} \left(\frac{\theta_4(q)}{\theta_3(q)}\right)^{\alpha v / 2} = \exp\Bigl(-2\alpha v q - v^2 q^2 + O(v q^3, v^2 q^4)\Bigr).
   \]
   Because every $q$ carries at most one power of $v$, $H_M(v) := H_M(c_\star, \mu, \mu, 0, \Delta_3(v), \Delta_4(v))$ is a polynomial in $v$ of degree at most $M$, with leading coefficient
   \[
   [v^M] H_M(v) = 16^{-M} [t^M] \exp(-2\alpha t - t^2) = \frac{(-1)^M}{16^M M!} H_M(\alpha),
   \]
   where $H_M(x)$ is the $M$-th physicist's Hermite polynomial.
4. **Nonvanishing of $H_M(\alpha)$ for every $M \geq 0$:**
   Since $m^{\mathrm{big}}_k \geq pp' + 1$, we have $X = m^{\mathrm{big}}_k - p' - p \geq (p - 1)(p' - 1) \geq 2$, hence $\alpha^2 = \frac{X^2}{pp'} \geq \frac{(p-1)^2(p'-1)^2}{pp'}$.
   - **$M = 0$:** $H_0(\alpha) = 1 \neq 0$.
   - **$M = 1$:** $H_1(\alpha) = 2\alpha > 0$.
   - **$M = 2$:** $H_2(\alpha) = 4\alpha^2 - 2 > 0$, because $\alpha^2 \geq \frac{(2-1)^2(3-1)^2}{2\cdot 3} = \frac{2}{3} > \frac{1}{2}$.
   - **$M = 3$:** $H_3(\alpha) = 4\alpha(2\alpha^2 - 3)$. Since $\frac{(x-1)^2}{x}$ is strictly increasing on $x \geq 1$, for all coprime $p' > p \geq 2$ with $(p, p') \neq (2, 3)$ we have $\frac{(p-1)^2(p'-1)^2}{pp'} \geq \min(\frac{1\cdot 16}{2\cdot 5}, \frac{4\cdot 9}{3\cdot 4}) = \frac{8}{5} > \frac{3}{2}$, so $2\alpha^2 - 3 > 0$. For $(p, p') = (2, 3)$, the unique interior weight is $(r, s) = (1, 1)$ ($h = 0$): at $k = 1$, $m^{\mathrm{big}}_1 = 7$, $X = 2$, $\alpha^2 = \frac{2}{3} \neq \frac{3}{2}$; for $k \geq 2$, $X \geq 2\cdot 6 + 1 - 5 = 8$, $\alpha^2 \geq \frac{32}{3} > \frac{3}{2}$. Thus $H_3(\alpha) \neq 0$ in all cases.
   - **$M \geq 4$:** By Schur's irreducibility theorems (I. Schur, *Einige Sätze über Primzahlen mit Anwendungen auf Irreduzibilitätsfragen, II*, Sitzungsber. Preuss. Akad. Wiss. Berlin Phys.-Math. Kl. **14** (1929), 370–391, for $H_{2m}(x)$; I. Schur, *Affektlose Gleichungen in der Theorie der Laguerreschen und Hermiteschen Polynome*, J. Reine Angew. Math. **165** (1931), 52–58, for $H_{2m+1}(x)/x$), for every $m \geq 1$ the polynomials $H_{2m}(x)$ and $H_{2m+1}(x)/x$ are irreducible over $\mathbb{Q}$. Consequently, as polynomials in $t = x^2$ of degree $m$, $H_{2m}(\sqrt{t})$ and $H_{2m+1}(\sqrt{t})/\sqrt{t}$ are irreducible over $\mathbb{Q}$ (any nontrivial factorization over $\mathbb{Q}$ would pull back via $t = x^2$ to a nontrivial factorization of $H_{2m}(x)$ or $H_{2m+1}(x)/x$). For $m \geq 2$ (i.e. $M \geq 4$), an irreducible polynomial of degree $m \geq 2$ over $\mathbb{Q}$ has no rational root, whereas $\alpha^2 = X^2/(pp') \in \mathbb{Q}$. Therefore $H_M(\alpha) \neq 0$ for all $M \geq 4$.

Hence $H_M(v) \not\equiv 0$ in $\mathbb{C}[v]$, so the leading Laurent coefficient $\lim_{\Delta \to \lambda}(\Delta - \lambda)^k H_N$ is a nonzero polynomial in $v$ on our line, and therefore nonzero for indeterminate external weights. $\square$
