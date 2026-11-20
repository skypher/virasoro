# Structural Analysis for Irreducible Minimal-Model Torus One-Point Traces (`T_IRR`)

## 1. The target object

Fix coprime integers $p, p' \ge 2$, the minimal-model parameter $b_\star^2 = -p'/p$, central charge
$$c_\star = 1 - \frac{6(p'-p)^2}{pp'},$$
and an interior Kac weight $\lambda = h_{r,s}(b_\star)$ ($1 \le r \le p-1$, $1 \le s \le p'-1$, labeled so that $n_1 = p'r + ps < pp'$). Let $M(c_\star, \lambda)$ be the Verma module, $J(c_\star, \lambda) = \operatorname{rad} B$ its maximal proper submodule, and $L(c_\star, \lambda) = M(c_\star, \lambda)/J(c_\star, \lambda)$ the irreducible quotient.

For an external weight $d \in \mathbb{C}$, let $\rho_N(c_\star, \lambda, d): M_N \times M_N \to \mathbb{C}$ be the Virasoro-covariant three-point bilinear form of a primary operator $V_d(1)$ normalized by $\rho_0(v_\lambda, v_\lambda) = 1$. Whenever $J_N \subset \operatorname{rad} \rho_N$ for all $N \ge 0$, $\rho_N$ descends to a bilinear form $\bar\rho_N$ on $L_N$, and since the induced Shapovalov form $\bar B_N$ is nondegenerate on $L_N$, the irreducible torus one-point trace
$$\mathcal{T}^{\mathrm{irr}}_{c_\star, \lambda, d}(q) = \operatorname{Tr}_{L(c_\star, \lambda)}\bigl(q^{L_0 - \lambda} V_d(1)\bigr) = \sum_{N=0}^\infty T^{\mathrm{irr}}_N(c_\star, \lambda, d)\, q^N, \qquad T^{\mathrm{irr}}_N = \operatorname{Tr}_{L_N}(\bar B_N^{-1}\bar\rho_N),$$
is well-defined.

## 2. Exact small-case discoveries (bottom-up findings)

1. **Exact descent test (`(2,5)` and `(3,4)`, $N \le 8$)**:
   - Descent holds ($J_N \subset \operatorname{rad}\rho_N$) at Lee--Yang $(2,5)$ $(\lambda, d) = (-1/5, -1/5)$, Ising $(3,4)$ $(1/16, 1/2)$, Tricritical Ising $(4,5)$ $(3/80, 3/5), (3/80, 3/2), (3/80, 1/10)$, and $d=0$; it fails at $N=2$ for forbidden Ising $(1/16, 1/16)$.
   - Ising $(3,4)$, $\lambda = 1/16$, $d = 1/2$: $T^{\mathrm{irr}}_N = [q^N]\prod_{m=1}^\infty (1-q^m)$ ($1, -1, -1, 0, 0, 1, 0, 1, 0, \dots$), verified directly from quotient Gram/rho through $N = 10$ and from the BGG formula through $N = 30$.
   - Lee--Yang $(2,5)$, $\lambda = -1/5$, $d = -1/5$: $T^{\mathrm{irr}}_N = 1, 2/5, 17/25, 98/125, 714/625, 18768/15625, \dots$ has pure $5$-power denominators through $N = 25$, while $F^{\mathrm{Verma}}_N(c_\star, -1/5, -1/5)$ has primes $7, 11, 13, 17, 19, \dots$ in its denominators.
2. **Why naive Verma limits and 2/3-parameter rays fail to isolate $T^{\mathrm{irr}}_N$**:
   - At fusion-allowed $d$, $F^{\mathrm{Verma}}_N(c_\star, \Delta, d)$ is regular at $\Delta = \lambda$, yet $F^{\mathrm{Verma}}_N(c_\star, \lambda, d) \ne T^{\mathrm{irr}}_N(c_\star, \lambda, d)$ starting at $N = \ell_1$:
     - Lee--Yang $N=2$: $F^{\mathrm{Verma}}_2 - T^{\mathrm{irr}}_2 = 3/7 = \sigma^+_1/\gamma^+_1$.
     - Ising $N=2, 3, 4$: $F^{\mathrm{Verma}}_N - T^{\mathrm{irr}}_N = 15/7, 155/77, 85/77$.
   - Fixed-$c_\star$ 2-parameter rays $(\Delta, d) = (\lambda + x, d_\star + \alpha x)$ cancel the discrepancy at $N = 2, 3$ for Ising ($\alpha = 5$) but fail at $N = 4$ (where $\alpha = 17/19$ is required). Three-parameter rays $(b_\star + c_b x, \lambda + x, d_\star + c_d x)$ similarly vary continuously with $(c_b, c_d)$ because they mix the $x$- and $d$-derivatives of $\rho_N$ on $J^1$.
3. **The true structure discovered from the small cases**:
   - At Lee--Yang $N = 0..10$ (crossing layer 2 at $N = 9$), Ising $N = 0..10$ (crossing layer 2 at $N = 10$), and Tricritical Ising $N = 0..8$ (all three nonzero fusion weights $h_{1,3}, h_{3,1}, h_{3,3}$):
     - $F^{\mathrm{Verma}}_N(c_\star, \Delta, d)$ has pole order $0$ at $\Delta = \lambda$ and at every BGG weight $\mu^\pm_j$.
     - The discrepancy $F^{\mathrm{Verma}}_N(\lambda) - T^{\mathrm{irr}}_N(\lambda)$ decomposes cleanly across Jantzen layers via the ratios $c(\mu \to \nu) = \sigma(\mu \to \nu)/\gamma(\mu \to \nu)$.
     - Even more remarkably, $c_{R,S}(t; 2k+1, 2m+1)$ at generic $t = b^2$ equals a shifted rectangle product
       $$c_{R,S}(t; 2k+1, 2m+1) = \frac{\prod_{a=1-R}^R \prod_{b'=1-S}^S ((a+k)t + (b'+m))}{\prod_{a=1-R}^R \prod_{b'=1-S}^S (at + b')} = \frac{\Psi_{2k+1, 2m+1}(h_{R,-S}; b)}{\Psi_{2k+1, 2m+1}(h_{R,S}; b)},$$
       which automatically satisfies the BGG diamond cocycle identity $c(\lambda \to \mu^+_1)c(\mu^+_1 \to \mu^\pm_2) = c(\lambda \to \mu^-_1)c(\mu^-_1 \to \mu^\pm_2) = c(\lambda \to \mu^\pm_2)$.

## 3. Complete algebraic proof architecture (three main theorems)

### Theorem 1 (Fusion-descent and exact regularity iff)
Let $d \in \mathbb{C}$. The following three conditions are equivalent:
1. $\rho(c_\star, \lambda, d)$ descends to a well-defined bilinear form on $L(c_\star, \lambda)$;
2. $d \in \mathcal{F}_{p,p'}(r,s) := \{h_{2k+1, 2m+1}(b_\star) : 0 \le k < \min(r, p-r),\; 0 \le m < \min(s, p'-s)\}$ (and the pair $(k, m)$ is uniquely determined by $d$);
3. $F^{\mathrm{Verma}}_N(c_\star, \Delta, d)$ is regular (pole order $0$) at $\Delta = \lambda$ for every $N \ge 0$.

**Proof mechanism**:
- $(1) \iff (2)$: symmetry of $\rho$, Ward induction on PBW level showing $J^1 = U(\mathrm{Vir}_-)w^+_1 + U(\mathrm{Vir}_-)w^-_1 \subset \operatorname{rad}\rho \iff P_{r,s}(b_\star, \lambda, d) = P_{p-r, p'-s}(b_\star, \lambda, d) = 0$, plus elementary coprime arithmetic showing $u_1 + u_2 \le 2p - 2 < 2p$ so every common root has a unique representative $(u,v) = (2k+1, 2m+1)$ in the intersection box.
- $(3) \implies (2)$: since $\max(\ell^+_1, \ell^-_1) < \min(\ell^+_2, \ell^-_2)$ unconditionally, the top-layer formula at $k = 1$ (`paper.tex` Theorem 5.9) gives a nonzero simple pole at $N = \min(\ell^+_1, \ell^-_1)$ or $N = \max(\ell^+_1, \ell^-_1)$ whenever $P_{r,s} \ne 0$ or $P_{p-r,p'-s} \ne 0$.
- $(2) \implies (3)$: proven in TWO independent ways:
  - *Intrinsic Jantzen vertex filtration*: on $\mathcal{J}^{(k)} = \{a(x) \in M(c_\star, \lambda+x)[[x]] : B_x(a(x), M) \subset x^k \mathbb{C}[[x]]\}$, induction on $k \ge 0$ shows $\rho_x(\mathcal{J}^{(k)}, \mathcal{J}^{(k)}) \subset x^k \mathbb{C}[[x]]$, $\rho^{(k)} = [x^k]\rho_x$ is well-defined on $J^{(k)}$ and obeys the exact $V_d(1)$ Ward identity, and $J^{(k+1)} \subset \operatorname{rad} \rho^{(k)}$ (since every BGG embedding label $(R, S)$ has $R \ge \min(r, p-r) > k$ and $S \ge \min(s, p'-s) > m$, and any $w \in J^{(k+1)}$ is singular in both $M(\mu^+_k)$ and $M(\mu^-_k)$). Diagonalizing the symmetric matrix $B_x$ over the DVR $\mathbb{C}[[x]]$ cancels $x^{e_i}$ in every diagonal summand of $\operatorname{Tr}(B_x^{-1} R_x)$, yielding regularity at $x = 0$ and the Jantzen trace decomposition
    $$F_N(c_\star, \lambda, d) = T^{\mathrm{irr}}_N(c_\star, \lambda, d) + \sum_{j=1}^{j_N(\lambda)} \sum_{\pm} \frac{\sigma^\pm_j(\lambda)}{\gamma^\pm_j(\lambda)} T^{\mathrm{irr}}_{N - \ell^\pm_j}(c_\star, \mu^\pm_j, d).$$
  - *Confluent recursion vanishing*: along $d(b) = h_{2k+1, 2m+1}(b)$, every Kac label $(R, S)$ colliding at $\lambda$ (or any BGG weight $\mu^\pm_j$) satisfies $R \ge k+1$ and $S \ge m+1$, so $R_{R,S}(b, d(b)) \equiv 0$ identically in $b$; hence $F_N(c(b), \Delta, d(b))$ is jointly holomorphic in $(b, \Delta)$ near $(b_\star, \mu^\pm_j)$.

### Theorem 2 (Generic first-layer Jantzen vertex ratio via the two-weight fusion product rule)
For generic $b$ ($t = b^2$), $R, S \ge 1$, and $0 \le k \le R-1$, $0 \le m \le S-1$, with $d = h_{2k+1, 2m+1}(b)$,
$$c_{R,S}(t; 2k+1, 2m+1) = \frac{\partial_\Delta \rho_{\Delta, d}(\chi_{R,S}, \chi_{R,S})|_{\Delta=h_{R,S}}}{\partial_\Delta B_\Delta(\chi_{R,S}, \chi_{R,S})|_{\Delta=h_{R,S}}} = \frac{\prod_{a=1-R}^R \prod_{b'=1-S}^S ((a+k)t + (b'+m))}{\prod_{a=1-R}^R \prod_{b'=1-S}^S (at + b')} = \frac{\Psi_{2k+1, 2m+1}(h_{R,-S}; b)}{\Psi_{2k+1, 2m+1}(h_{R,S}; b)}.$$

**Proof mechanism (10 lines, completely elementary)**:
Consider the symmetric two-weight pairing $f_d(x_1, x_2) = \rho_{h_{R,S}+x_1, h_{R,S}+x_2; d}(\chi_{R,S}, \chi_{R,S})$. At $x_2 = 0$, the right vector $\chi_{R,S}$ is singular, so uniqueness of the three-point pairing between $M(h_{R,S}+x_1)$ and $M(h_{R,-S})$ gives
$$f_d(x_1, 0) = C_{R,S}(b)\, P_{R,S}(b; h_{R,S}+x_1, d)\, \rho_{h_{R,S}+x_1, h_{R,-S}; d}(\chi_{R,S}, v_{h_{R,-S}}).$$
Since $P_{R,S}(b; h_{R,S}, d) = 0$, differentiating at $x_1 = 0$ and using symmetry $f_d(x_1, x_2) = f_d(x_2, x_1)$ gives
$$\left.\frac{d}{dx}\right|_{x=0} f_d(x, x) = 2\, C_{R,S}(b)^2\, \partial_{\Delta_1} P_{R,S}(b; h_{R,S}, d)\, P_{R,S}(b; h_{R,-S}, d).$$
At $d = 0$, $\rho_{\Delta, \Delta; 0} \equiv B_\Delta$, so dividing by the $d = 0$ formula cancels $2\, C_{R,S}(b)^2$ identically. Grouping the $4RS - 1$ nonzero linear factors of $\partial_{\Delta_1} P_{R,S}(h_{R,S}, d) P_{R,S}(h_{R,-S}, d)$ into the four quadrants of $[1-R, R] \times [1-S, S] \setminus \{(-k,-m)\}$ gives the exact rectangle ratio, and Euler's reflection formula separates it into $\Psi_{2k+1, 2m+1}(h_{R,-S}; b)/\Psi_{2k+1, 2m+1}(h_{R,S}; b)$.

### Theorem 3 (Generalized Rocha--Caridi / BGG identity and exact fixed-$b_\star$ confluence for $\mathcal{T}^{\mathrm{irr}}$)
For every minimal model $b_\star^2 = -p'/p$, every interior Kac weight $\lambda = h_{r,s}(b_\star)$, and every $d = h_{2k+1, 2m+1}(b_\star) \in \mathcal{F}_{p,p'}(r,s)$,
$$\mathcal{T}^{\mathrm{irr}}_{c_\star, \lambda, d}(q) = \mathcal{F}^{\mathrm{Verma}}_{c_\star, \lambda, d}(q) + \sum_{j=1}^\infty (-1)^j \left( \frac{\Psi_{u,v}(\mu^+_j)}{\Psi_{u,v}(\lambda)}\, q^{\ell^+_j}\, \mathcal{F}^{\mathrm{Verma}}_{c_\star, \mu^+_j, d}(q) + \frac{\Psi_{u,v}(\mu^-_j)}{\Psi_{u,v}(\lambda)}\, q^{\ell^-_j}\, \mathcal{F}^{\mathrm{Verma}}_{c_\star, \mu^-_j, d}(q) \right),$$
where every ratio $\Psi_{u,v}(\mu^\pm_j)/\Psi_{u,v}(\lambda) \in \mathbb{Q}^\times$ is finite and nonzero, given by the product of box ratios along any BGG path $\lambda \to \mu^\pm_j$.

**Proof mechanism (2-layer $t$-Jantzen telescoping — bypasses higher Jantzen layers completely!)**:
1. Every weight $\mu$ in the BGG orbit of $\lambda$ lies in Class $\mathrm{III}_-$ (Astashkevich 1997 Theorem A(c)), with two primitive singular vectors of Kac labels $(R_1, S_1)$ and $(R_2, S_2)$ leading to $\nu_1, \nu_2$, satisfying $R_1 S_1 \ne R_2 S_2$ and $\min(R_i/p, S_i/p') < 1$ (so $\gamma_{R_i, S_i}(b_\star) \ne 0$).
2. At generic $b = b_\star + t$, the 1-layer Jantzen trace formula on $M(c(b), h_{R_1, S_1}(b))$ gives
   $$F_N(c(b), h_{R_1, S_1}(b), d(b)) = \operatorname{Tr}_{V_{R_1, S_1}(b)_N}(V_{d(b)}(1)) + c_{R_1, S_1}(b; u, v)\, F_{N - R_1 S_1}(c(b), h_{R_1, -S_1}(b), d(b)).$$
3. As $t \to 0$, $V_{R_1, S_1}(b_\star + t)_N$ is a free $\mathbb{C}[[t]]$-module of rank $p(N) - p(N - R_1 S_1)$ specializing to $M(c_\star, \mu)/M(c_\star, \nu_1)$, which has length $2$ with composition factors $L(c_\star, \mu)$ and $L(c_\star, \nu_2)$ (since $M(\nu_1) \cap M(\nu_2) = \operatorname{rad} M(\nu_2)$). Because $h_{R_1, S_1}(b) - h_{R_2, S_2}(b)$ has a simple zero at $b_\star$ ($\partial_t \propto R_2 S_2 - R_1 S_1 \ne 0$) and $\gamma_{R_2, S_2}(b_\star) \ne 0$, the $t$-Jantzen filtration on $V_{R_1, S_1}(b_\star + t)$ has exact length $2$ ($J_t^2 = 0$, also confirming Astashkevich Theorem C(e)). Since both $B(\chi_{R_2, S_2}, \chi_{R_2, S_2})$ and $\rho(\chi_{R_2, S_2}, \chi_{R_2, S_2})$ vanish identically along $\Delta = h_{R_2, S_2}(b)$, the chain rule equates the $t$-derivative ratio to the $\Delta$-derivative ratio $c_{R_2, S_2}(b_\star; u, v) = \Psi(\nu_2)/\Psi(\mu)$.
4. Taking $t \to 0$ (using joint holomorphicity of $F_N(c(b), \Delta, d(b))$ at $(b_\star, \mu)$ and $(b_\star, \nu_1)$) yields the exact two-term identity
   $$\widetilde{\mathcal{T}}(\mu) + \widetilde{\mathcal{T}}(\nu_2) = \widetilde{\mathcal{F}}(\mu) - \widetilde{\mathcal{F}}(\nu_1), \qquad \widetilde{\mathcal{T}}(\mu) := \Psi(\mu) q^{\mu-\lambda} \mathcal{T}^{\mathrm{irr}}(\mu).$$
5. Taking the alternating sum along the BGG chain $\lambda \to \mu^-_1 \to \mu^+_2 \to \mu^-_3 \to \cdots$ telescopes every $\widetilde{\mathcal{T}}(\mu^\pm_j)$ ($j \ge 1$) to zero, giving Theorem 3.
6. Combining Theorem 3 with Theorem 4.3 of the companion torus paper (`paper.tex`) computes every coefficient $T^{\mathrm{irr}}_N(c_\star, \lambda, d)$ exactly by finite algebraic confluence from the generic Poghossian--HJS recursion with no numerical $\varepsilon$-limit. In the single-index cases $d = h_{1, 2m+1}(b_\star)$ (dually $h_{2k+1, 1}(b_\star)$), the truncated recursion ($S \le m$, resp. $R \le k$) has **zero collisions and zero $b$-poles at $b = b_\star$ to all orders $N \ge 1$**.
