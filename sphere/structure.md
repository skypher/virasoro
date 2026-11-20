# Structural analysis: sphere four-point Virasoro blocks at rational $b^2$

This document analyzes the mathematical structure of the Verma-module $s$-channel sphere four-point Virasoro block before any construction or large computation, comparing it point by point against the finished torus one-point paper (`paper.tex` at `299e8a0`).

## 1. Exact objects and the two normalizations

Let $\Vir$ be the Virasoro algebra with $[L_m, L_n] = (m-n)L_{m+n} + \frac{c}{12}(m^3-m)\delta_{m+n,0}$, $c(b) = 1 + 6Q^2$, $Q = b + b^{-1}$, and Kac weights $h_{r,s}(b) = \frac{1}{4}(Q^2 - (rb + sb^{-1})^2)$. Fix four indeterminate external weights $\Delta_1, \Delta_2, \Delta_3, \Delta_4$ (parametrized when convenient by $\Delta_i = \frac{1}{4}(Q^2 - \Lambda_i^2)$) and an internal weight $\Delta$.

### 1.1. The $z$-expansion (cross-ratio normalization)

For a partition $Y = (y_1 \geq \dots \geq y_\ell)$ of $N$, define the three-point descendant pairing
$$\gamma_Y(\Delta; \Delta_a, \Delta_b) := \langle \Delta | L_{y_\ell} \cdots L_{y_1} \Phi_b(1) | \Delta_a \rangle,$$
where $\Phi_b(z)$ is primary of weight $\Delta_b$ with $\langle \Delta | \Phi_b(z) | \Delta_a \rangle = z^{\Delta - \Delta_b - \Delta_a}$. Because $L_n |\Delta_a\rangle = 0$ for $n > 0$ and $[L_n, \Phi_b(z)] = \mathcal{D}_n \Phi_b(z)$ with the scalar differential operator $\mathcal{D}_n = z^n(z\partial_z + (n+1)\Delta_b)$, commuting modes to the right from the inside out yields an exact closed-form product:
$$\gamma_Y(\Delta; \Delta_a, \Delta_b) = \prod_{j=1}^{\ell(Y)} \Bigl( \Delta + \sum_{i = j+1}^{\ell(Y)} y_i + y_j \Delta_b - \Delta_a \Bigr) \in \mathbb{Z}[\Delta, \Delta_a, \Delta_b],$$
completely independent of $c$. By the dual Ward identity for $\langle \Delta_4 | \Phi_3(z) L_{-y_1}\cdots L_{-y_\ell} |\Delta\rangle$,
$$\langle \Delta_4 | \Phi_3(1) | L_{-Y}\Delta \rangle = \gamma_Y(\Delta; \Delta_4, \Delta_3), \qquad \langle L_{-Y}\Delta | \Phi_2(1) | \Delta_1 \rangle = \gamma_Y(\Delta; \Delta_1, \Delta_2).$$
The $s$-channel Verma-module sphere four-point block is $\mathcal{F}_\Delta(z) = z^{\Delta - \Delta_1 - \Delta_2} \mathcal{B}(c, \Delta, \Delta_i; z)$ with $\mathcal{B}(z) = \sum_{N \geq 0} \mathcal{B}_N(c, \Delta, \Delta_i) z^N$, $\mathcal{B}_0 = 1$, and
$$\mathcal{B}_N(c, \Delta, \Delta_i) = \sum_{|Y| = |Y'| = N} \gamma_Y(\Delta; \Delta_4, \Delta_3) \bigl(G_N(c, \Delta)^{-1}\bigr)_{Y,Y'} \gamma_{Y'}(\Delta; \Delta_1, \Delta_2).$$
Each $\mathcal{B}_N$ is a rational function of $(c, \Delta)$ and a polynomial in $\Delta_1, \dots, \Delta_4$, with denominator dividing $\det G_N(c, \Delta)$.

**Large-$\Delta$ behavior of $\mathcal{B}_N$:** Since $\deg_\Delta \gamma_Y = \ell(Y)$ and $(G_N^{-1})_{Y,Y'} \sim \delta_{Y,Y'} K_Y^{-1} \Delta^{-\ell(Y)}$, each $\mathcal{B}_N$ grows as a **polynomial of degree $N$ in $\Delta$** (leading term $\frac{\Delta^N}{2^N N!}$ from $Y = Y' = (1^N)$). Therefore $\mathcal{B}_N$ does **not** vanish at $\Delta = \infty$; its partial-fraction expansion in $\Delta$ has a nontrivial polynomial part of degree $N$.

### 1.2. The elliptic $H$-function (nome normalization)

Let $q = q(z) = \exp(-\pi K'(z)/K(z))$ be the elliptic nome, whose inverse is $z(q) = \theta_2(q)^4/\theta_3(q)^4 = 16q(1 - 8q + 44q^2 - \cdots) \in 16q(1 + q\mathbb{Z}[[q]])$, with $1 - z(q) = \theta_4(q)^4/\theta_3(q)^4$. Zamolodchikov's elliptic $H$-function is defined as the formal power series
$$H(c, \Delta, \Delta_i; q) = 1 + \sum_{N \geq 1} H_N(c, \Delta, \Delta_i) (16q)^N$$
by
$$H(c, \Delta, \Delta_i; q) = \left(\frac{z(q)}{16q}\right)^{\Delta - \frac{c-1}{24}} \bigl(1 - z(q)\bigr)^{\Delta_2 + \Delta_3 - \frac{c-1}{24}} \theta_3(q)^{4(\Delta_1+\Delta_2+\Delta_3+\Delta_4) - \frac{c-1}{2}} \mathcal{B}\bigl(c, \Delta, \Delta_i; z(q)\bigr).$$
Writing $\Phi(c, \Delta, \Delta_i; q) := \left(\frac{z(q)}{16q}\right)^{\Delta - \frac{c-1}{24}} (1 - z(q))^{\Delta_2+\Delta_3-\frac{c-1}{24}} \theta_3(q)^{4\sum \Delta_j - \frac{c-1}{2}}$, observe:
1. $\Phi(c, \Delta, \Delta_i; q) \in 1 + q\,\mathbb{Q}[c, \Delta, \Delta_1, \dots, \Delta_4][[q]]$ has **polynomial** coefficients in $(c, \Delta, \Delta_1, \dots, \Delta_4)$ and constant term $1$ (no poles in $c$ or $\Delta$!).
2. Consequently, each $H_N(c, \Delta, \Delta_i)$ is an explicit finite $\mathbb{Q}[c, \Delta, \Delta_1, \dots, \Delta_4]$-linear combination of $\mathcal{B}_0, \dots, \mathcal{B}_N$, and conversely each $\mathcal{B}_N$ is an explicit finite $\mathbb{Q}[c, \Delta, \Delta_1, \dots, \Delta_4]$-linear combination of $H_0, \dots, H_N$.
3. **Why $H_N$ is the canonical normalization for S1:** For $N \geq 1$, $H_N(c, \Delta, \Delta_i)$ has **no polynomial part in $\Delta$**, i.e. $\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_i) = \delta_{N,0}$, so $H_N$ is purely a sum of principal parts in $\Delta$ and obeys Zamolodchikov's $\Delta$-recursion at generic $b$. Once $H_N$ is computed by finite algebraic confluence at fixed $b_\star$, $\mathcal{B}_N$ is recovered identically via $\mathcal{B}(z) = \Phi(q(z))^{-1} H(q(z))$ (a finite polynomial transformation at each level $N$ introducing no $b$-singularities).

## 2. What transfers verbatim from the torus paper (`paper.tex`)

Every statement in `paper.tex` that depends only on the Virasoro Verma module $M(c, \Delta)$, the Shapovalov Gram matrix $G_N(c, \Delta)$, and the formal-germ expansion of a generic residue recursion transfers verbatim:

1. **Collision classes** (`Def 3.1`, `Prop 3.2`): $\Lambda_N(b_\star)$, $\mathcal{C}^\star_{\lambda,N}$, and the minimal-model collision characterization $(r',s') = (r+p\ell, s+p'\ell)$ or $(p\ell-r, p'\ell-s)$.
2. **Shapovalov / Jantzen theory** (`Lem 5.1`, `Def 5.2`, `Lem 5.3`, `Lem 5.4`, `Lem 5.6`, `Lem 5.7`, `Thm 5.8`):
   - Local Smith exponents of $G_N(c_\star, \lambda + x)$ equal the dimensions of the Jantzen layers $J^i_N(c_\star, \lambda) = (W^+_i + W^-_i)_N$.
   - The Jantzen forms $B^i$ are contravariant, $B^k$ is nondegenerate on the top layer $J^k_N$, and $[x^{-k}] G_N(c_\star, \lambda + x)^{-1} = \iota (B^k)^{-1} \iota^*$.
   - The pole order of $G_N(c_\star, \Delta)^{-1}$ at $\Delta = \lambda$ is exactly $j_N(\lambda)$, giving the **upper bound** $m^\star_{\lambda, N} \leq j_N(\lambda)$ immediately for both $\mathcal{B}_N$ and $H_N$ (since $\Phi$ is polynomial in $\Delta$).
   - Every singular vector $w$ of level $\ell$ has nonzero $L_{-1}^\ell$-coefficient (`Lem 5.7`), and the normalized generic singular vector $\chi_{r,s}(b)$ is regular at every $b_\star \in \mathbb{C}^\times$ (`Lem 6.6`).
3. **Generic crossing scalar and non-collision lemma** (`Prop 6.2` eq. `(6.1)`, `Lem 6.3`): $\beta_{\chi_{r,s}(b)} = \mathcal{A}_{r,s}(b)^{-1}$, and away from $b_\star^2 \in \mathbb{Q}$ there are no collisions, no shifted self-poles, and no poles of $\mathcal{A}_{r,s}$.
4. **Formal-germ confluence engine** (`Sec 7`: `Def 7.1`, `Lem 7.2`, `Def 7.3`, `Lem 7.4`, `Lem 7.5`, and the proof of `Thm 4.3`):
   - Replace $K_\star = \mathbb{Q}(b_\star, d)$ by $K_\star = \mathbb{Q}(b_\star, \Delta_1, \Delta_2, \Delta_3, \Delta_4)$ and $R_a(t) = \mathcal{R}_{r,s}(b_\star+t, d)$ by $R^{\mathrm{sph}}_a(t) = \mathcal{A}_{r,s}(b_\star+t) P_{r,s}(b_\star+t, \Delta_1, \Delta_2) P_{r,s}(b_\star+t, \Delta_4, \Delta_3)$.
   - **Provided** the generic Zamolodchikov recursion for $H_N$ holds (which needs the large-$\Delta$ limit $\lim_{\Delta \to \infty} H_N = \delta_{N,0}$!), the entire Section 7 proof of finite algebraic confluence and exact partial-fraction identification with the inverse-Shapovalov $H_N$ goes through word for word!

## 3. What changes from the torus paper

1. **Rank-one external pairing instead of the torus matrix $\rho_N$:**
   - Torus: $\operatorname{Tr}(G_N^{-1} \rho_N^T)$, where $\rho_N$ is a $p(N)\times p(N)$ matrix depending on $(c, \Delta, d)$.
   - Sphere: $\gamma^{(43)}(\Delta)^T G_N^{-1} \gamma^{(21)}(\Delta)$, rank one, independent of $c$.
2. **Three-point factorization instead of torus factorization (`Lem 5.5`):**
   For any singular vector $w \in M(c, h)$ of level $\ell$ (at arbitrary fixed $c$, not only generic),
   $$\langle L_{-Z} w | \Phi_2(1) | \Delta_1 \rangle = \langle w | \Phi_2(1) | \Delta_1 \rangle \, \gamma_Z(h+\ell; \Delta_1, \Delta_2),$$
   $$\langle \Delta_4 | \Phi_3(1) | L_{-Z} w \rangle = \langle \Delta_4 | \Phi_3(1) | w \rangle \, \gamma_Z(h+\ell; \Delta_4, \Delta_3).$$
   Proof: $L_{-Z}|h+\ell\rangle \mapsto L_{-Z} w$ is a Virasoro module homomorphism $M(c, h+\ell) \to M(c, h)$, and the Ward recursion determines every matrix element uniquely from its highest-weight value.
3. **Fusion polynomials instead of $\mathcal{P}_{r,s}(b, d)$:**
   At generic $b$, for the normalized singular vector $\chi_{r,s}(b)$ ($L_{-1}^{rs}$-coefficient $1$),
   $$P_{r,s}(b, \Delta_a, \Delta_b) := \langle \chi_{r,s}(b) | \Phi_b(1) | \Delta_a \rangle = \prod_{\substack{j = 1-r \\ \text{step } 2}}^{r-1} \prod_{\substack{l = 1-s \\ \text{step } 2}}^{s-1} \frac{\Lambda_a + \Lambda_b + jb + lb^{-1}}{2}\,\frac{\Lambda_a - \Lambda_b + jb + lb^{-1}}{2}$$
   (sign/normalization to be verified explicitly at low levels against $\gamma_Y$ and CCY eq. `(2.22)` / Ribault eq. `(4.3.7)`!). Note $P_{r,s}$ is a polynomial in $(\Delta_a, \Delta_b)$ of degree $rs$ in $\Delta_b - \Delta_a$ (leading term $(\Delta_b - \Delta_a)^{rs}$ since $\chi_{r,s}$ has $L_{-1}^{rs}$-coefficient $1$ and $\gamma_{(1^{rs})} = (\Delta + \Delta_b - \Delta_a)_{rs}$).
4. **Top Jantzen layer formula (`S2_TOP`):**
   For $\ell_k \leq N < \ell_{k+1}$, let $\pi^\pm_k(\Delta_a, \Delta_b) = \langle w^\pm_k | \Phi_b(1) | \Delta_a \rangle$ (with $w^\pm_k$ normalized to $L_{-1}^{\ell^\pm_k}$-coefficient $1$) and $\gamma^\pm_k = B^k(w^\pm_k, w^\pm_k)$ (the exact same Jantzen norms as in the torus paper!).
   Then:
   - For the $z$-expansion:
     $$\lim_{\Delta \to \lambda} (\Delta - \lambda)^k \mathcal{B}_N(c_\star, \Delta, \Delta_i) = \sum_{\pm : \ell^\pm_k \leq N} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_2, \Delta_1)}{\gamma^\pm_k}\,\mathcal{B}_{N - \ell^\pm_k}(c_\star, \mu^\pm_k, \Delta_i).$$
   - For the elliptic $H$-function: multiplying the generating series identity by $\Phi(c_\star, \Delta, \Delta_i; q)$ and using $(16q)^{-\lambda} z(q)^{\lambda + \ell^\pm_k} = (16q)^{\ell^\pm_k} (16q)^{-\mu^\pm_k} z(q)^{\mu^\pm_k}$ yields the **identical** formula for $H_N$:
     $$\lim_{\Delta \to \lambda} (\Delta - \lambda)^k H_N(c_\star, \Delta, \Delta_i) = \sum_{\pm : \ell^\pm_k \leq N} \frac{\pi^\pm_k(\Delta_4, \Delta_3)\,\pi^\pm_k(\Delta_2, \Delta_1)}{\gamma^\pm_k}\,H_{N - \ell^\pm_k}(c_\star, \mu^\pm_k, \Delta_i).$$
   - Moreover, since $w^\pm_{2j+1} = \chi_{R^\pm, S^\pm}(b_\star)$ and $w^\pm_{2j}$ are singular descendants of $w^+_{2j-1} = \chi_{R_0, S_0}(b_\star)$, three-point factorization gives exact product formulas for $\pi^\pm_k$ at every $k$:
     $$\pi^+_{2j+1} = P_{r+jp, s+jp'}, \quad \pi^-_{2j+1} = P_{(j+1)p-r, (j+1)p'-s},$$
     $$\pi^+_{2j} = P_{r+(j-1)p, s+(j-1)p'}\, P_{(2j-1)p+r, p'-s}, \quad \pi^-_{2j} = P_{r+(j-1)p, s+(j-1)p'}\, P_{p-r, (2j-1)p'+s}.$$

## 4. Structural analysis of the two core problems & anticipated risks

### 4.1. S2 sharpness (`S2_SHARP`): why two external pairs make sharpness dramatically simpler than on the torus

On the torus, there was a single external variable $d$, and the two branches $\tau^+_k(d)$ and $\tau^-_k(d)$ shared roots at $d = 0, 1, h_{1,\pm 3}$, forcing a deep $\ell$-adic analysis via Feigin–Fuchs Fock factorization and level polynomiality.

On the sphere, the two pairs $(\Delta_1, \Delta_2)$ and $(\Delta_3, \Delta_4)$ are independent:
1. **Strict branch isolation in $(\Delta_3, \Delta_4)$:** For every $k \geq 1$, the Coulomb momenta $m^+_k, m^-_k > 0$ are distinct ($m^+_{2j+1} - m^-_{2j+1} = 2(n_1 - pp') < 0$ and $m^+_{2j} - m^-_{2j} = 2n_0 \neq 0$). Let $\mathrm{big}, \mathrm{small} \in \{+,-\}$ satisfy $m^{\mathrm{big}}_k > m^{\mathrm{small}}_k$ (equivalently $\ell^{\mathrm{big}}_k > \ell^{\mathrm{small}}_k$, so $M^{\mathrm{small}} = N - \ell^{\mathrm{small}}_k \geq 1$ on every boundary and two-vector level).
   With $b_\star = i\sqrt{p'/p}$, every root of $P_{R,S}(b_\star, \Delta_4, \Delta_3)$ is a line $\Lambda_3 \pm \Lambda_4 = -i\frac{jp' - lp}{\sqrt{pp'}}$ with $|jp' - lp| \leq Rp' + Sp - p' - p$.
   Hence the hyperplane
   $$\Lambda_3 - \Lambda_4 = i\alpha, \qquad \alpha := \frac{X}{\sqrt{pp'}}, \qquad X := m^{\mathrm{big}}_k - p' - p > 0,$$
   with $v := -i(\Lambda_3 + \Lambda_4)$ remaining free:
   - kills $\pi^{\mathrm{big}}_k(\Delta_4, \Delta_3) \equiv 0$ (via $j = -(R^{\mathrm{big}}-1)$, $l = S^{\mathrm{big}}-1$), and
   - does **not** kill $\pi^{\mathrm{small}}_k(\Delta_4, \Delta_3)$ (all $\Lambda_3 - \Lambda_4$ factors satisfy $X + jp' - lp \geq m^{\mathrm{big}}_k - m^{\mathrm{small}}_k > 0$, and all $\Lambda_3 + \Lambda_4$ factors are monic linear in $v$).
2. **Collapse of $H_M$ at $(\Delta_1, \Delta_2) = (\mu^{\mathrm{small}}_k, 0)$:**
   At $\Delta_2 = 0$, $\Delta_1 = \mu := \mu^{\mathrm{small}}_k$:
   - $\Lambda_1 \pm \Lambda_2 = i\frac{m^{\mathrm{small}}_k \pm (p'-p)}{\sqrt{pp'}}$, both strictly larger in magnitude than $m^{\mathrm{small}}_k - p' - p$ (since $m^{\mathrm{small}}_k \geq n_1 \geq p' + p$), so $\pi^{\mathrm{small}}_k(0, \mu) \neq 0$ unconditionally.
   - $\gamma_Y(\mu; \mu, 0) = 0$ for every $|Y| \geq 1$, so $\mathcal{B}_m(c_\star, \mu, \mu, 0, \Delta_3, \Delta_4) = \delta_{m,0}$ for all $m \leq M^{\mathrm{small}}$.
   - Therefore, through order $q^{M^{\mathrm{small}}}$, $H(q)$ collapses to the explicit theta product $g(q) (\theta_3(q)\theta_4(q))^{v^2/4} (\theta_4(q)/\theta_3(q))^{\alpha v/2}$.
   - Extracting $[v^M] H_M$ yields $\frac{(-1)^M}{16^M M!} H_M(\alpha)$ (physicist's Hermite polynomial).
   - **Anticipated risk R1 (S2 for $H_N$):** Verify Schur's irreducibility theorem for $H_M$ (1931) in context (or check an elementary proof / check if any edge case exists for $M = 1, 2, 3$ — already checked: $\alpha^2 \geq 2/3 > 1/2$ rules out $M = 2$, and $X^2 = \frac{3}{2}pp'$ has no solution with $X > pp' - p' - p$ and $m^{\mathrm{big}}_k \neq 8$ at $(2,3)$, ruling out $M = 3$).
   - **Anticipated risk R2 (S2 for $\mathcal{B}_N$, the $z$-expansion):** Since $\mathcal{B}_M = 0$ at $(\Delta_1, \Delta_2) = (\mu, 0)$, the $z$-expansion needs a separate nonvanishing witness on the hyperplane $\Lambda_3 - \Lambda_4 = i\alpha$. Candidate witnesses: (a) the degenerate $(2,1)$ point $\Delta_2 = h_{2,1}(b_\star)$, $\Lambda_1 = \Lambda_\mu + b_\star$ (where $\mathcal{B}(z) = (1-z)^\kappa {}_2F_1(A(v), B; C; z)$ is an explicit Gauss hypergeometric function!), or (b) first-order derivative $\partial_{\Delta_1}|_{\Delta_1=\mu, \Delta_2=0}$. Test both in Step 3!

### 4.2. S1 confluence (`S1_ASYMP` and `S1_CONF`): the genuine hard step

`S1_CONF` (the formal-germ confluence theorem assuming the generic Zamolodchikov recursion for $H_N$) transfers almost verbatim from `paper.tex` Section 7.

**The genuine hard step and highest anticipated risk (R3) is `S1_ASYMP`:**
$$\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_1, \Delta_2, \Delta_3, \Delta_4) = \delta_{N, 0} \qquad \text{for every } N \geq 0.$$
Ribault (2026 §4.3.4) explicitly flags that no complete rigorous proof exists in the literature. We must NOT leave `S1_ASYMP` as an unproved assumption!

**Candidate custom mathematical routes for `S1_ASYMP`:**
1. **Route A — Algebraic pillow map & Wick-contraction asymptotics:**
   In the pillow conformal frame $T^2/\mathbb{Z}_2$, the sphere four-point block becomes
   $$\mathcal{F}_\Delta^{\mathrm{pillow}}(q) = (16q)^{\Delta - \frac{c}{24}} \prod_{m=1}^\infty (1 - q^{2m})^{-1/2} H_\Delta(q),$$
   which is a matrix element $\langle \psi_{34} | q^{L_0 - c/24} | \psi_{12} \rangle$ in $M(c, \Delta)$.
   Notice that $\prod_{m \geq 1} (1 - q^{2m})^{-1/2} = \sum_{(k_m)} \prod_{m \geq 1} \frac{(2k_m-1)!!}{(2k_m)!!} q^{2m k_m}$, and the diagonal large-$\Delta$ Gram norm of $L_{-m}^{2k_m}|\Delta\rangle$ is $(2k_m)! (2m)^{2k_m} \Delta^{2k_m}$.
   The ratio $\frac{((2k_m-1)!! (2m\Delta)^{k_m})^2}{(2k_m)! (2m)^{2k_m} \Delta^{2k_m}} = \frac{(2k_m-1)!!}{(2k_m)!!}$ matches the exact coefficient of $(1 - q^{2m})^{-1/2}$!
   **Hypothesis to test immediately on $N = 1, \dots, 6$:** Does the pillow state $|\psi_{12}\rangle$ (obtained from $\Phi_2(1)|\Delta_1\rangle$ by the explicit Virasoro change-of-coordinates map $x \mapsto u(x)$ on the pillow!) satisfy the exact large-$\Delta$ degree bound $\deg_\Delta \langle \Delta | L_Y |\psi_{12}\rangle \leq \lfloor \ell(Y)/2 \rfloor$, with equality iff every part of $Y$ has even multiplicity $2k_m$, and leading coefficient $\prod_m (2k_m-1)!! (\pm 2m\Delta)^{k_m}$?!
   If YES, this would yield a **completely algebraic, self-contained proof of $\lim_{\Delta \to \infty} H_N = \delta_{N,0}$**, analogous to Lemma 4.1 of the torus paper!
2. **Route B — Heisenberg / Fock oscillator basis (`Besken–Datta–Kraus` style, adapted to fixed $c$, $\Delta \to \infty$):**
   In the Fock module $\mathcal{F}(\alpha)$ with $\Delta = \frac{1}{2}\alpha(\alpha - 2q_0)$ ($q_0$ fixed, $\alpha \to \infty$), the Virasoro modes are $L_n = \alpha a_n + \frac{1}{2}\sum_{k \neq 0, n} {:}a_k a_{n-k}{:} - q_0(n+1)a_n$, so the change-of-basis matrix $B_N(q_0, \alpha)$ becomes diagonal $\sim \alpha^{\ell(Y)}$ as $\alpha \to \infty$, and the 3-point vertex operator $\Phi_2(z)$ in the pillow coordinate becomes a free-boson vertex operator $e^{\beta \varphi(u)}$ whose pillow correlator is an explicit Gaussian / theta function!
3. **Route C — Algebraic differential equation / Zamolodchikov monodromy / $c$-recursion:**
   Fallback if Routes A and B encounter an obstruction.

## 5. Immediate plan (bottom up)

1. **Step 3a (exact small cases for S2 and S1):** Write an exact rational/symbolic script `sphere/tools/exact_sphere_block.py` computing $\mathcal{B}_N$ and $H_N$ directly from Shapovalov Gram matrices $G_N$ and the closed-form 3-point vectors $\gamma_Y$ at $(p,p') = (2,3), (2,5), (3,4)$ for the first levels (reaching double poles: $N \leq 6$ at $(2,3)$, $N \leq 7$ at $(3,4)$ and $(2,5)$, and up to $N = 10$ via rational reconstruction!).
   - Verify exact conventions ($P_{r,s}$ signs, Ribault's $(2,3)$ $N=5$ double pole $\frac{3}{11200\Delta^2}\cdots$, Ising $N=7$ double pole with $\gamma_7 = -700700$).
   - Verify our S2 sharpness specialization ($\Lambda_3 - \Lambda_4 = i\alpha$, $\Delta_2 = 0, \Delta_1 = \mu$, Hermite $H_M(\alpha)$) AND test the $\mathcal{B}_N$ sharpness witness!
2. **Step 3b (test Route A / Route B for `S1_ASYMP`):** Directly test the pillow change-of-coordinate state $|\psi_{12}\rangle$ and its Virasoro / Fock large-$\Delta$ asymptotics at levels $N = 1, \dots, 6$ in exact symbolic arithmetic!
3. **Step 4:** Prove `S1_ASYMP`, `S1_CONF`, `S2_TOP`, `S2_SHARP` completely in `sphere/notes/`, build exact audit scripts, draft `sphere/paper.tex`, and submit batched self-contained review packets to `jander` and `yang2` (cc `main`).
