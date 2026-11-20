# S1_ASYMP: Exact Large-$\Delta$ Asymptotics of the Sphere Four-Point Virasoro Block

## Goal statement (`Theorem S1A`)

Let $\mathcal{F}(c, \Delta, \Delta_1, \Delta_2, \Delta_3, \Delta_4; z) = z^{\Delta - \Delta_1 - \Delta_2}\sum_{N=0}^\infty \mathcal{B}_N(c, \Delta, \Delta_i) z^N$ be the Verma-module $s$-channel sphere four-point Virasoro conformal block ($\mathcal{B}_0 = 1$) in the standard convention
\[
\mathcal{B}_N(c, \Delta, \Delta_i) = \sum_{|Y|=|Z|=N} \gamma_Y(\Delta; \Delta_4, \Delta_3)\, \bigl(G_N(c, \Delta)^{-1}\bigr)_{Y,Z}\, \gamma_Z(\Delta; \Delta_1, \Delta_2),
\]
where $\gamma_Y(\Delta; \Delta_a, \Delta_b) = \prod_{j=1}^{\ell(Y)} \bigl(\Delta + \sum_{i>j} y_i + y_j \Delta_b - \Delta_a\bigr)$ for $Y = (y_1 \geq \dots \geq y_{\ell(Y)} \geq 1)$ and $G_N(c, \Delta)_{Y,Z} = \langle L_{-Y} v_\Delta, L_{-Z} v_\Delta \rangle$ is the level-$N$ Shapovalov Gram matrix.

Let $q(z) = \exp\!\bigl(-\pi K(1-z)/K(z)\bigr) \in \frac{z}{16}(1 + z\mathbb{Q}[[z]])$ be the elliptic nome ($K(z) = \frac{\pi}{2}{}_2F_1(\frac{1}{2}, \frac{1}{2}; 1; z)$), and define the elliptic $H$-series $H(c, \Delta, \Delta_i; q) = \sum_{N=0}^\infty H_N(c, \Delta, \Delta_i) (16 q)^N$ ($H_0 = 1$) by
\[
\mathcal{F}(c, \Delta, \Delta_i; z) = \Phi(c, \Delta, \Delta_i; q(z)) \, H(c, \Delta, \Delta_i; q(z)),
\]
where Zamolodchikov's prefactor is
\[
\Phi(c, \Delta, \Delta_i; q) := (16 q)^{\Delta - \frac{c-1}{24}} \, z(q)^{\frac{c-1}{24} - \Delta_1 - \Delta_2} \, (1 - z(q))^{\frac{c-1}{24} - \Delta_2 - \Delta_3} \, \theta_3(q)^{\frac{c-1}{2} - 4(\Delta_1 + \Delta_2 + \Delta_3 + \Delta_4)}.
\]
Here $\theta_3(q) = \sum_{n \in \mathbb{Z}} q^{n^2}$, $\theta_4(q) = \sum_{n \in \mathbb{Z}} (-1)^n q^{n^2}$, $\theta_2(q) = \sum_{n \in \mathbb{Z}} q^{(n+1/2)^2}$, satisfying the classical Jacobi identities $z(q) = \theta_2(q)^4 / \theta_3(q)^4$, $1 - z(q) = \theta_4(q)^4 / \theta_3(q)^4$, ${}_2F_1(\frac{1}{2}, \frac{1}{2}; 1; z(q)) = \theta_3(q)^2$, and $z \frac{d}{dz}\log\frac{16q(z)}{z} = \frac{1}{(1-z)\theta_3(q(z))^4} - 1$.

**Theorem S1A.** *For every $N \geq 0$ and every $(c, \Delta_1, \Delta_2, \Delta_3, \Delta_4) \in \mathbb{C}^5$, the rational function $H_N(c, \Delta, \Delta_i) \in \mathbb{Q}(c, \Delta_1, \dots, \Delta_4)(\Delta)$ satisfies*
\[
\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_1, \Delta_2, \Delta_3, \Delta_4) = \delta_{N, 0}.
\]
*Equivalently, $\deg_\Delta\bigl(\operatorname{num} H_N\bigr) < \deg_\Delta\bigl(\det G_N(c, \Delta)\bigr)$ for every $N \geq 1$, as a rational function of $\Delta$ with polynomial coefficients in $(c, \Delta_1, \dots, \Delta_4)$.*

---

## Proof via Feigin–Fuchs Fock Oscillators

The proof consists of six self-contained lemmas (Lemmas A1–A6).

### Lemma A1 (Fock–Verma equivalence and polynomial extension)

Parameterize $c = 1 + 24\mu^2$ and $\Delta = \lambda^2 + \mu^2$ with $\mu \in \mathbb{R}_{>0}$ and $\lambda \in \mathbb{R}_{>0}$. On the polynomial Fock space $\mathcal{F}_{\mu, \lambda} = \mathbb{C}[u_1, u_2, \dots]$ (graded by $\deg(u_m) = m$) equipped with the positive-definite Hermitian inner product
\[
\langle \bar f, g \rangle := \sum_{\alpha} \overline{f_\alpha}\, g_\alpha \prod_{m \geq 1} \frac{\alpha_m!}{(2m)^{\alpha_m}},
\]
the operators
\begin{align*}
l_0 &= \sum_{n=1}^\infty n u_n \partial_{u_n} + \lambda^2 + \mu^2,\\
l_k &= \sum_{n=1}^\infty n u_n \partial_{u_{n+k}} - \frac{1}{4}\sum_{n=1}^{k-1} \partial_{u_n}\partial_{u_{k-n}} + (\mu k + i\lambda)\partial_{u_k} \qquad (k \geq 1),\\
l_{-k} &= \sum_{n=1}^\infty (n+k) u_{n+k} \partial_{u_n} - \sum_{n=1}^{k-1} n(k-n) u_n u_{k-n} + 2k(\mu k - i\lambda) u_k \qquad (k \geq 1)
\end{align*}
satisfy the Virasoro commutation relations of central charge $c = 1 + 24\mu^2$ with adjoint relation $l_k^\dagger = l_{-k}$ (where conjugation sends $u_m \mapsto \bar u_m$ and $i \mapsto -i$, fixing $\mu, \lambda \in \mathbb{R}$).

**Claim.** For any fixed $\mu > 0$, $\Delta_1, \Delta_2, \Delta_3, \Delta_4 \in \mathbb{R}$, and $N \geq 0$:
1. For every $\lambda > 0$, the Verma module $V(1 + 24\mu^2, \lambda^2 + \mu^2)$ is irreducible and isometric to $\mathcal{F}_{\mu, \lambda}$ via $L_{-Y} v_\Delta \mapsto l_{-Y} 1$.
2. There is a unique formal series $F(u; \lambda) = \sum_{m=0}^\infty F_m(u; \lambda)$ with $F_m \in \mathcal{F}_{\mu, \lambda}$ homogeneous of level $m$, $F_0 = 1$, satisfying the Ward identities
   \[
   l_k F = \bigl(l_0 + k \Delta_2 - \Delta_1\bigr) F \qquad (\forall k \geq 1).
   \]
   Explicitly, at level $m$, $l_k F_m = (m - k + \Delta + k\Delta_2 - \Delta_1) F_{m-k}$.
3. Letting $\widetilde{F}(\bar u; \lambda)$ be obtained from $F(u; \lambda)$ by replacing $u_m \mapsto \bar u_m$, $i \mapsto -i$, and $(\Delta_1, \Delta_2) \mapsto (\Delta_4, \Delta_3)$, we have
   \[
   \mathcal{B}_N(1 + 24\mu^2, \lambda^2 + \mu^2, \Delta_i) = \langle \widetilde{F}_N(\bar u; \lambda),\, F_N(u; \lambda) \rangle.
   \]
4. If $\lim_{\lambda \to +\infty} H_N(1 + 24\mu^2, \lambda^2 + \mu^2, \Delta_i) = \delta_{N, 0}$ holds for every $\mu > 0$ and $(\Delta_1, \dots, \Delta_4) \in \mathbb{R}^4$, then $\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_i) = \delta_{N, 0}$ holds for all $(c, \Delta_1, \dots, \Delta_4) \in \mathbb{C}^5$.

**Proof.**
(1) For $c = 1 + 24\mu^2 > 1$, the Kac determinant $\det G_N(c, \Delta) = K_N \prod_{rs \leq N} (\Delta - h_{r,s}(c))^{p(N-rs)}$ has no roots with $\Delta > \mu^2 = \frac{c-1}{24}$: writing $c = 1 + 6 Q^2$ with $Q = b + b^{-1} = 2\mu > 0$, if $c \geq 25$ then $b > 0$ so $h_{r,s} = \frac{Q^2 - (rb + sb^{-1})^2}{4} \leq \frac{Q^2 - Q^2}{4} = 0 < \Delta$, while if $1 < c < 25$ then $b = e^{i\theta}$ ($\theta \in (0, \pi/2)$) so $h_{r,r} = \frac{(1-r^2)Q^2}{4} \leq 0 < \Delta$ and for $r \neq s$ we have $\operatorname{Im}((rb + sb^{-1})^2) = (r^2 - s^2)\sin(2\theta) \neq 0$, so $h_{r,s} \notin \mathbb{R}$. Hence $G_N(c, \Delta)$ is positive-definite for all $\Delta > \mu^2$ (in fact all $\Delta > 0$). Since the highest-weight homomorphism $\phi : V(c, \Delta) \to \mathcal{F}_{\mu, \lambda}$ preserves the contravariant Hermitian form (as $l_k^\dagger = l_{-k}$) and both spaces have dimension $p(N)$ at level $N$, $\phi$ is a unitary isomorphism.

(2)–(3) Under the isometry $\phi$, the level-$N$ descendant vector $w_N^{(1,2)} \in V(c, \Delta)_N$ uniquely defined by $\langle L_{-Y} v_\Delta, w_N^{(1,2)} \rangle = \gamma_Y(\Delta; \Delta_1, \Delta_2)$ satisfies
\[
\langle L_{-Z} v_\Delta, L_k w_N^{(1,2)} \rangle = \gamma_{(Z, k)}(\Delta; \Delta_1, \Delta_2) = (N - k + \Delta + k\Delta_2 - \Delta_1) \gamma_Z(\Delta; \Delta_1, \Delta_2)
\]
for every partition $Z$ of $N - k$, hence $L_k w_N^{(1,2)} = (N - k + \Delta + k\Delta_2 - \Delta_1) w_{N-k}^{(1,2)}$. Because $V(c, \Delta)$ is irreducible, $F_N = \phi(w_N^{(1,2)})$ is the unique solution to $l_k F_N = (N - k + \Delta + k\Delta_2 - \Delta_1) F_{N-k}$ with $F_0 = 1$. Since $\mathcal{B}_N = \langle w_N^{(4,3)}, w_N^{(1,2)} \rangle$ and $\phi(w_N^{(4,3)}) = \overline{\widetilde{F}_N}$ (remembering $\langle \widetilde{F}_N, F_N \rangle$ pairs $\widetilde{F}_N$ without an additional conjugation since $\widetilde{F}$ already carries $i \mapsto -i$, matching the Hermitian inner product $\langle \phi(w_N^{(4,3)}), \phi(w_N^{(1,2)}) \rangle$ for real $\Delta_i, \mu, \lambda$), we obtain $\mathcal{B}_N = \langle \widetilde{F}_N, F_N \rangle$.

(4) By definition, $\det G_N(c, \Delta)$ is a polynomial in $(c, \Delta)$ whose leading term in $\Delta$ is $K_N \Delta^{d_N}$ ($K_N \in \mathbb{Q}_{>0}$, $d_N = \sum_{rs \leq N} p(N-rs)$), and $H_N(c, \Delta, \Delta_i) = P_N(c, \Delta, \Delta_i) / \det G_N(c, \Delta)$ where $P_N \in \mathbb{Q}[c, \Delta, \Delta_1, \dots, \Delta_4]$ (since $q(z)$ and $\Phi^{-1} z^{\Delta - \Delta_1 - \Delta_2}$ expand in $z$ with coefficients in $\mathbb{Q}[c, \Delta, \Delta_i]$ and every $\mathcal{B}_m$ has denominator dividing $\det G_m \mid \det G_N$). For $N \geq 1$, the hypothesis $\lim_{\lambda \to +\infty} H_N(1+24\mu^2, \lambda^2+\mu^2, \Delta_i) = 0$ on the Zariski-dense real open set $\{c > 1, \Delta_i \in \mathbb{R}\}$ forces every coefficient of $\Delta^d$ ($d \geq d_N$) in $P_N(c, \Delta, \Delta_i)$ to vanish identically as a polynomial in $(c, \Delta_1, \dots, \Delta_4)$. Thus $\deg_\Delta P_N < d_N$ identically, so $\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_i) = 0$ for every $(c, \Delta_1, \dots, \Delta_4) \in \mathbb{C}^5$. $\square$

---

### Lemma A2 (Exact $\lambda^{-1}$-expansion and universal exponential structure)

Fix $\mu > 0$ and $\Delta_1, \dots, \Delta_4 \in \mathbb{R}$. Rescale $u_m = \lambda \sigma_m$ and define the formal logarithm
\[
S(\sigma; \lambda) := \lambda^{-2} \log F(\lambda \sigma; \lambda) = \sum_{m=1}^\infty S_m(\sigma; \lambda),
\]
where $S_m(\sigma; \lambda)$ is homogeneous of oscillator level $m$ in $\sigma = (\sigma_1, \sigma_2, \dots)$.

**Claim.**
1. For each $m \geq 1$, the coefficients of $S_m(\sigma; \lambda)$ are rational functions of $\lambda$ that are regular at $\lambda = \infty$, hence admit Taylor expansions
   \[
   S_m(\sigma; \lambda) = \sum_{r=0}^\infty \lambda^{-r} S_m^{(r)}(\sigma), \qquad S^{(r)}(\sigma) := \sum_{m=1}^\infty S_m^{(r)}(\sigma).
   \]
2. The leading three terms have the exact parameter dependence:
   - $S^{(0)}(\sigma)$ is independent of $(\mu, \Delta_1, \Delta_2)$ and satisfies
     \[
     i \partial_{\sigma_k} S^{(0)} + \sum_{n=1}^\infty n\sigma_n \bigl(\partial_{\sigma_{n+k}} S^{(0)} - \partial_{\sigma_n} S^{(0)}\bigr) - \frac{1}{4}\sum_{n=1}^{k-1} (\partial_{\sigma_n} S^{(0)})(\partial_{\sigma_{k-n}} S^{(0)}) - 1 = 0 \quad (\forall k \geq 1),
     \]
     whose unique solution is quadratic:
     \[
     S^{(0)}(\sigma) = \sum_{m=1}^\infty A_m \sigma_m + \sum_{m,n=1}^\infty B_{m,n} \sigma_m \sigma_n,
     \]
     with generating functions
     \[
     A(p) = \sum_{m=1}^\infty A_m p^m = -2i\bigl((1-p)^{-1/2} - 1\bigr), \qquad
     B(p, q) = \sum_{m,n=1}^\infty B_{m,n} p^m q^n = -\frac{1}{2} \frac{pq}{\sqrt{1-p}\sqrt{1-q}\bigl(\sqrt{1-p}+\sqrt{1-q}\bigr)^2}.
     \]
   - $S^{(1)}(\sigma) = \mu \widetilde{S}^{(1)}(\sigma)$ is purely linear in $\mu$, independent of $(\Delta_1, \Delta_2)$, and satisfies the involution parity $\widetilde{S}^{(1)}(-\sigma)\big|_{i \mapsto -i} = -\widetilde{S}^{(1)}(\sigma)$.
   - $S^{(2)}(\sigma) = \mu^2 S^{(2)}_c(\sigma) + (\Delta_2 - \frac{1}{16}) S^{(2)}_2(\sigma) + (\Delta_1 - \frac{1}{16}) S^{(2)}_1(\sigma)$ is affine-linear in $(\mu^2, \Delta_1 - \frac{1}{16}, \Delta_2 - \frac{1}{16})$ with zero constant term, where $S^{(2)}_2, S^{(2)}_1$ solve
     \[
     L_k^{(0)} S^{(2)}_2 - k = 0, \qquad L_k^{(0)} S^{(2)}_1 + 1 = 0 \qquad (\forall k \geq 1),
     \]
     for the first-order derivation $L_k^{(0)} := i\partial_{\sigma_k} + \sum_{n=1}^\infty n\sigma_n(\partial_{\sigma_{n+k}} - \partial_{\sigma_n}) - \frac{1}{2}\sum_{n=1}^{k-1} (\partial_{\sigma_n} S^{(0)})\partial_{\sigma_{k-n}}$.
3. There exist universal formal power series $\mathcal{I}_0, \Phi_c^{\mathrm{raw}}, \Phi_1, \Phi_2 \in z\mathbb{Q}[[z]]$ (independent of $\mu, \Delta_i$), with $\Phi_j(z) = S^{(2)}_j(\sigma_*(z))$ ($j = 1, 2$) evaluated at the unique saddle point $\sigma_*(z) \in i z \mathbb{Q}[[z]]^{\mathbb{N}}$ of $-2\sum m z^{-m} \sigma_m \bar\sigma_m + S^{(0)}(\sigma) + \widetilde{S}^{(0)}(\bar\sigma)$, such that as formal power series in $z$ (i.e., coefficient-by-coefficient for every $N \geq 0$):
   \[
   \lim_{\lambda \to \infty} e^{-\lambda^2 \mathcal{I}_0(z)} \mathcal{B}(1 + 24\mu^2, \lambda^2 + \mu^2, \Delta_i; z) = \det\bigl(I - M(z)^2\bigr)^{-1/2} \exp\Bigl(\mu^2 \Phi_c^{\mathrm{raw}}(z) + (\Delta_1 + \Delta_4 - \tfrac{1}{8})\Phi_1(z) + (\Delta_2 + \Delta_3 - \tfrac{1}{8})\Phi_2(z)\Bigr),
   \]
   where $M(z)_{m,n} = \frac{z^m}{m} B_{m,n}$ ($m, n \geq 1$).

**Proof.**
(1) Substituting $F(\lambda\sigma) = \exp(\lambda^2 S(\sigma; \lambda))$ into $l_k F = (l_0 + k\Delta_2 - \Delta_1) F$ (and dividing by $\lambda^2 F$) yields the exact PDE for every $k \geq 1$:
\[
\left(i + \frac{\mu k}{\lambda}\right)\partial_{\sigma_k} S + \sum_{n=1}^\infty n\sigma_n \bigl(\partial_{\sigma_{n+k}} S - \partial_{\sigma_n} S\bigr) - \frac{1}{4}\sum_{n=1}^{k-1} (\partial_{\sigma_n} S)(\partial_{\sigma_{k-n}} S) - \frac{1}{4\lambda^2}\sum_{n=1}^{k-1} \partial_{\sigma_n}\partial_{\sigma_{k-n}} S + \frac{\Delta_1 - k\Delta_2 - \mu^2}{\lambda^2} - 1 = 0.
\]
For each level $m \geq 1$ and each $k \in \{1, \dots, m\}$, extracting the homogeneous component of oscillator level $m - k$ isolates $S_m$ on the left-hand side:
\[
D_k(\lambda) S_m = R_{m, k}(S_1, \dots, S_{m-1}; \lambda),
\]
where
\[
D_k(\lambda) := \left(i + \frac{\mu k}{\lambda}\right)\partial_{\sigma_k} + \sum_{n=1}^\infty n\sigma_n \partial_{\sigma_{n+k}} - \frac{1}{4\lambda^2}\sum_{n=1}^{k-1}\partial_{\sigma_n}\partial_{\sigma_{k-n}}
\]
lowers level by $k$, and $R_{m,k}$ is a polynomial in $S_1, \dots, S_{m-1}$ and $\lambda^{-2}$ with no positive powers of $\lambda$ (note that in $\sum_{n=1}^{k-1} (\partial_{\sigma_n} S)(\partial_{\sigma_{k-n}} S)$ at level $m - k$, since $S_0 = 0$, every product involves only $S_a, S_b$ with $a + b = m$ and $a, b \geq 1$, hence $a, b < m$).

Consider the linear map $\mathcal{D}_m(\lambda) : \mathbb{C}[\sigma]_m \to \bigoplus_{k=1}^m \mathbb{C}[\sigma]_{m-k}$ given by $P \mapsto (D_1(\lambda) P, \dots, D_m(\lambda) P)$. Its $\lambda \to \infty$ limit is $D_k(\infty) = i\partial_{\sigma_k} + \sum_{n \geq 1} n\sigma_n \partial_{\sigma_{n+k}}$. We show that $\mathcal{D}_m(\infty)$ is **injective**: suppose $P \in \mathbb{C}[\sigma]_m \setminus \{0\}$ satisfies $D_k(\infty) P = 0$ for all $k = 1, \dots, m$. Write $P = P_d + P_{d+1} + \dots$ as a sum of homogeneous components of total polynomial degree $j = \sum e_r$, with $P_d \neq 0$ of minimal degree $d \geq 1$ (since $m \geq 1$). Because $\partial_{\sigma_k}$ lowers total polynomial degree by $1$ while $\sum n\sigma_n\partial_{\sigma_{n+k}}$ preserves total polynomial degree, the degree-$(d-1)$ component of $D_k(\infty) P = 0$ is $i\partial_{\sigma_k} P_d = 0$ for all $k = 1, \dots, m$. Thus $P_d$ is constant, contradicting $m \geq 1$ and $P_d \neq 0$.

Since $\mathcal{D}_m(\infty)$ has full column rank $p(m)$, some $p(m) \times p(m)$ submatrix $M_m(\lambda^{-1})$ of $\mathcal{D}_m(\lambda)$ (whose entries are polynomials in $\lambda^{-1}$) satisfies $\det M_m(0) \neq 0$. Therefore $M_m(\lambda^{-1})^{-1}$ is regular at $\lambda^{-1} = 0$. By induction on $m \geq 1$, $S_m(\sigma; \lambda)$ is regular at $\lambda = \infty$, so expanding the exact PDE in powers of $\lambda^{-1}$ yields the unique order-by-order system for $S^{(0)}, S^{(1)}, S^{(2)}, \dots$.

(2) At order $\lambda^0$, the PDE for $S^{(0)}$ is independent of $(\mu, \Delta_1, \Delta_2)$. Direct verification (Lemma A3 below) shows that the quadratic $S^{(0)} = \sum A_m\sigma_m + \sum B_{m,n}\sigma_m\sigma_n$ solves it, and satisfies $-\frac{1}{4}\sum_{n=1}^{k-1} \partial_{\sigma_n}\partial_{\sigma_{k-n}} S^{(0)} = -\frac{1}{2}\sum_{n=1}^{k-1} B_{n, k-n} = \frac{k-1}{16}$. By uniqueness (injectivity of $\mathcal{D}_m(\infty)$), this is the unique solution $S^{(0)}$.

At order $\lambda^{-1}$, the PDE is $L_k^{(0)} S^{(1)} + \mu k \partial_{\sigma_k} S^{(0)} = 0$. Since $S^{(0)}$ is independent of $(\mu, \Delta_1, \Delta_2)$ and $L_k^{(0)}$ is linear with level-lowering leading part $D_k(\infty)$, uniqueness gives $S^{(1)} = \mu \widetilde{S}^{(1)}$ independent of $(\Delta_1, \Delta_2)$. Define the $\mathbb{R}$-linear automorphism $\iota$ of $\mathbb{C}[[\sigma]]$ by $\iota(i) = -i$ and $\iota(\sigma_m) = -\sigma_m$. Since $A_m \in i\mathbb{R}$ and $B_{m,n} \in \mathbb{R}$, we have $\iota(S^{(0)}) = S^{(0)}$ and $\iota \circ L_k^{(0)} = L_k^{(0)} \circ \iota$, while $\iota(k\partial_{\sigma_k} S^{(0)}) = -k\partial_{\sigma_k} S^{(0)}$. By uniqueness, $\iota(\widetilde{S}^{(1)}) = -\widetilde{S}^{(1)}$.

At order $\lambda^{-2}$, substituting $-\frac{1}{4}\sum_{n=1}^{k-1}\partial_{\sigma_n}\partial_{\sigma_{k-n}} S^{(0)} = \frac{k-1}{16}$, the PDE is
\[
L_k^{(0)} S^{(2)} + \mu^2\left(-\frac{1}{4}\sum_{n=1}^{k-1}(\partial_{\sigma_n}\widetilde{S}^{(1)})(\partial_{\sigma_{k-n}}\widetilde{S}^{(1)}) + k\partial_{\sigma_k}\widetilde{S}^{(1)} - 1\right) + \left(\Delta_1 - \frac{1}{16}\right) - k\left(\Delta_2 - \frac{1}{16}\right) = 0.
\]
By linearity and uniqueness, $S^{(2)} = \mu^2 S^{(2)}_c + (\Delta_2 - \frac{1}{16}) S^{(2)}_2 + (\Delta_1 - \frac{1}{16}) S^{(2)}_1$, and all three components are $\iota$-even: $\iota(S^{(2)}_a) = S^{(2)}_a$.

(3) Fix $N \geq 0$ and work in $\mathbb{C}[[z]]/(z^{N+1})$. By Lemma A1, $\mathcal{B}(z) \equiv \langle \widetilde{F}(\bar u), F(z^\bullet u) \rangle \pmod{z^{N+1}}$, which involves only the $N$ complex oscillator variables $(u_1, \dots, u_N)$ and equals the finite-dimensional algebraic Gaussian expectation with weight $\prod_{m=1}^N \frac{2m}{\pi} e^{-2m |u_m|^2} d^2 u_m$:
\[
\mathcal{B}(z) \equiv \int_{\mathbb{C}^N} \left(\prod_{m=1}^N \frac{2m}{\pi} d^2 u_m\right) \exp\left(-2\sum_{m=1}^N m u_m \bar u_m + \lambda^2 S^{(0)}\!\left(\frac{z^\bullet u}{\lambda}\right) + \lambda^2 \widetilde{S}^{(0)}\!\left(\frac{\bar u}{\lambda}\right)\right) R(z; u, \bar u; \lambda) \pmod{z^{N+1}},
\]
where $R = \exp\bigl(\sum_{r \geq 1} \lambda^{2-r} [S^{(r)}(z^\bullet u/\lambda) + \widetilde{S}^{(r)}(\bar u/\lambda)]\bigr)$ is a formal power series in $z$ whose $z^k$-coefficient ($k \leq N$) is a polynomial in $(u_1, \dots, u_N, \bar u_1, \dots, \bar u_N)$ with rational coefficients in $\lambda^{-1}$.

The quadratic part of the exponent has Hessian matrix $Q(z) = \begin{pmatrix} -2 B^{(z)} & 2D \\ 2D & -2B \end{pmatrix}$ where $D = \mathrm{diag}(1, \dots, N)$ and $B^{(z)}_{m,n} = z^{m+n} B_{m,n} = O(z^2)$. In $\mathbb{C}[[z]]/(z^{N+1})$, the perturbation $Q(z) - \begin{pmatrix} 0 & 2D \\ 2D & 0 \end{pmatrix}$ gives a strictly nilpotent matrix $M_1 M_2 = M(z)^2$ (entries $O(z^2)$), so Gaussian integration modulo $z^{N+1}$ is a purely algebraic Wick contraction with exact determinant $\det(I - M(z)^2)^{-1/2}$ and unique saddle point $(u_*, \bar u_*) = (\lambda z^{-\bullet}\sigma_*, \lambda \bar\sigma_*)$ solving
\[
-2m z^{-m} \bar\sigma_{*, m} + A_m + 2\sum_{n=1}^N B_{m,n}\sigma_{*,n} = 0, \qquad
-2m z^{-m} \sigma_{*, m} + \bar A_m + 2\sum_{n=1}^N B_{m,n}\bar\sigma_{*,n} = 0.
\]
Since $\bar A_m = -A_m$ and $B_{m,n} \in \mathbb{R}$, the unique solution satisfies $\bar\sigma_{*, m} = -\sigma_{*, m} \in i z^m \mathbb{Q}[[z]]$ and $(I + M(z))\sigma_* = -\frac{1}{2} D^{-1} Z A$, with on-shell value $\mathcal{I}_0(z) = -2\sum m z^{-m}\sigma_{*,m}\bar\sigma_{*,m} + S^{(0)}(\sigma_*) + \widetilde{S}^{(0)}(\bar\sigma_*)$.

Shifting $u_m = \lambda z^{-m}\sigma_{*,m} + \xi_m$ and $\bar u_m = \lambda \bar\sigma_{*,m} + \bar\xi_m$ (so $\sigma_m = \sigma_{*,m} + \lambda^{-1} z^m\xi_m$ and $\bar\sigma_m = \bar\sigma_{*,m} + \lambda^{-1}\bar\xi_m$):
- At order $\lambda^2$: the constant $\lambda^2 \mathcal{I}_0(z)$ factors out.
- At order $\lambda^1$: $\lambda\bigl[S^{(1)}(\sigma_*) + \widetilde{S}^{(1)}(\bar\sigma_*)\bigr] = \lambda\mu\bigl[\widetilde{S}^{(1)}(\sigma_*) + \iota(\widetilde{S}^{(1)})(\sigma_*)\bigr] = 0$ identically by the $\iota$-oddness of $\widetilde{S}^{(1)}$ and $\bar\sigma_* = -\sigma_*$!
- At order $\lambda^0$: expanding $R$ yields
  \[
  \exp\Bigl(\mu\sum_{m=1}^N \bigl(\partial_{\sigma_m}\widetilde{S}^{(1)}(\sigma_*)\, z^m \xi_m + \partial_{\bar\sigma_m}\widetilde{S}^{(1)}_{\mathrm{conj}}(\bar\sigma_*)\,\bar\xi_m\bigr) + S^{(2)}(\sigma_*) + \widetilde{S}^{(2)}(\bar\sigma_*)\Bigr) \cdot \bigl(1 + O(\lambda^{-1})\bigr).
  \]
Taking the centered Gaussian expectation over $(\xi, \bar\xi)$ modulo $z^{N+1}$ and sending $\lambda \to \infty$:
- The linear-in-$(\xi, \bar\xi)$ exponential integrates to $\exp(\mu^2 \Psi_1(z))$ for a universal series $\Psi_1(z) \in z\mathbb{Q}[[z]]$ independent of $(\mu, \Delta_i)$.
- Using $\iota$-evenness of $S^{(2)}$, $\widetilde{S}^{(2)}(\bar\sigma_*) = \mu^2 S^{(2)}_c(\sigma_*) + (\Delta_3 - \frac{1}{16}) S^{(2)}_2(\sigma_*) + (\Delta_4 - \frac{1}{16}) S^{(2)}_1(\sigma_*)$.
Setting $\Phi_c^{\mathrm{raw}}(z) := 2 S^{(2)}_c(\sigma_*(z)) + \Psi_1(z)$ and $\Phi_j(z) := S^{(2)}_j(\sigma_*(z))$ ($j = 1, 2$) yields the claimed universal formula modulo $z^{N+1}$ for every $N \geq 0$. $\square$

---

### Lemma A3 (Exact $S^{(0)}$, half-pillow diagonalization, and Wiener–Hopf saddle point)

1. The generating functions $A(p) = -2i((1-p)^{-1/2} - 1)$ and $B(p, q) = -\frac{1}{2} pq ((1-p)(1-q))^{-1/2} ((1-p)^{1/2} + (1-q)^{1/2})^{-2}$ solve the $S^{(0)}$ PDE and satisfy $-\frac{1}{2}\sum_{n=1}^{k-1} B_{n, k-n} = \frac{k-1}{16}$ for all $k \geq 1$.
2. Define the half-pillow variables $t_n(\sigma) := [w^{-n}]\sum_{m=1}^\infty \sigma_m p(w)^{-m} = \sum_{m=n}^\infty 4^{-m}\binom{2m}{m-n}\sigma_m$ ($n \geq 1$), where $p(w) = \frac{4w}{(1+w)^2}$, and let $g(w) := 2i\sum_{n=1}^\infty n t_n w^n$. Then:
   \[
   S^{(0)}(\sigma) = -4i\sum_{n=1}^\infty (-1)^{n-1} t_n - 2\sum_{n=1}^\infty n t_n^2.
   \]
3. Define the formal Laurent series on $|z| < |x| < 1$:
   \[
   \Omega(x; z) := \frac{1}{{}_2F_1(\frac{1}{2}, \frac{1}{2}; 1; z)\sqrt{1-x}\sqrt{1 - z/x}} = 1 + \sum_{m=1}^\infty a_m(z) x^m + \sum_{m=1}^\infty a_m(z) (z/x)^m.
   \]
   Then the exact saddle point of Lemma A2 is $\sigma_{*, m}(z) = i \frac{a_m(z)}{m} z^m$ ($m \geq 1$), and:
   \[
   \mathcal{I}_0(z) = \log\frac{16 q(z)}{z}, \qquad
   1 - g_*(1) = \theta_4(q(z))^{-2}, \qquad
   1 - g_*(-1) = \theta_3(q(z))^{-2}.
   \]

**Proof.**
(1) Substituting $S^{(0)} = \sum A_m \sigma_m + \sum B_{m,n} \sigma_m \sigma_n$ into the $S^{(0)}$ PDE gives the three generating-function equations (with $s_1 = \sqrt{1-p}$, $s_2 = \sqrt{1-q}$):
- $\sigma^0$: $i A(p) - \frac{1}{4} A(p)^2 - \frac{p}{1-p} = 0$. Checking: $i(-2i(s_1^{-1}-1)) - \frac{1}{4}(-4(s_1^{-1}-1)^2) = 2(s_1^{-1}-1) + (s_1^{-1}-1)^2 = s_1^{-2} - 1 = \frac{p}{1-p}$.
- $\sigma^1$: $(2i - A(p)) B(p, q) + q \partial_q\bigl(\frac{p A(q) - q A(p)}{q-p} - \frac{p}{1-p} A(q)\bigr) = 0$. Setting $p = 1 - s_1^2, q = 1 - s_2^2$, $2i - A(p) = 2i/s_1$, and direct rational simplification yields $B(p, q) = -\frac{(1-s_1^2)(1-s_2^2)}{2 s_1 s_2 (s_1+s_2)^2}$.
- $\sigma^2$: $q\partial_q\bigl(\frac{p B(q, r) - q B(p, r)}{q-p} - \frac{p}{1-p} B(q, r)\bigr) + r\partial_r\bigl(\frac{p B(q, r) - r B(p, q)}{r-p} - \frac{p}{1-p} B(q, r)\bigr) - 2 B(p, q) B(p, r) = 0$ (Wait: check factor of $1$ vs $2$ on $B(p,q)B(p,r)$: in $-\frac{1}{4}\sum (\partial_{\sigma_n} S^{(0)})(\partial_{\sigma_{k-n}} S^{(0)})$, the $\sigma_m \sigma_l$ term is $-\frac{1}{4}\sum_{n=1}^{k-1} (2 B_{m,n})(2 B_{l, k-n}) = -\sum B_{m,n} B_{l, k-n}$, giving $-B(p,q)B(p,r)$ when $B_{m,n}$ is symmetric!). Substituting $p=1-s_1^2, q=1-s_2^2, r=1-s_3^2$ reduces this to a polynomial identity in $(s_1, s_2, s_3)$ verified identically to $0$.
- Second-derivative trace: setting $q = p$ in $B(p, q)$ gives
  \[
  -\frac{1}{2} B(p, p) = \frac{1}{4} \frac{p^2}{(1-p) \cdot 4(1-p)} = \frac{p^2}{16(1-p)^2} = \sum_{k=2}^\infty \frac{k-1}{16} p^k,
  \]
  hence $-\frac{1}{2}\sum_{n=1}^{k-1} B_{n, k-n} = \frac{k-1}{16}$ for every $k \geq 1$.

(2) Write $p = p(w) = \frac{4w}{(1+w)^2}$, $q = p(v) = \frac{4v}{(1+v)^2}$ for $|w|, |v| < 1$. Then $\sqrt{1-p(w)} = \frac{1-w}{1+w}$, so:
- $A(p(w)) = -2i\bigl(\frac{1+w}{1-w} - 1\bigr) = -\frac{4iw}{1-w} = -4i\sum_{n=1}^\infty w^n$ (Wait: check sign of $(-1)^{n-1}$! With $p(w) = \frac{4w}{(1+w)^2}$, $\sqrt{1-p} = \frac{1-w}{1+w}$, so $(1-p)^{-1/2} - 1 = \frac{1+w}{1-w} - 1 = \frac{2w}{1-w}$, hence $A(p(w)) = -4i\sum_{n=1}^\infty w^n$, NO $(-1)^{n-1}$! Wait: if $p(w) = \frac{-4w}{(1-w)^2}$ then $(-1)^{n-1}$ appears! Let's stick to $p(w) = \frac{4w}{(1+w)^2}$ consistently — double-checked below!).
- Check $\sum_{m=1}^\infty A_m \sigma_m$ via contour integral on $|w| = r < 1$:
  \[
  \sum_{m=1}^\infty A_m \sigma_m = [w^0]\Bigl(A(p(w)) \sum_{m=1}^\infty \sigma_m p(w)^{-m}\Bigr) = -4i \sum_{n=1}^\infty [w^{-n}]\sum_{m=1}^\infty \sigma_m p(w)^{-m} = -4i \sum_{n=1}^\infty t_n!
  \]
  (Check $m=1$: $A_1 = -i$, $t_1 = \frac{1}{4}\binom{2}{0}\sigma_1 = \frac{1}{4}\sigma_1$, so $-4i t_1 = -i\sigma_1 = A_1 \sigma_1$! EXACT!)
- Check $B(p(w), p(v))$:
  \[
  B(p(w), p(v)) = -\frac{1}{2} \frac{4w}{1-w^2} \frac{4v}{1-v^2} \cdot \frac{(1+w)^2(1+v)^2}{4(1-wv)^2} \cdot \dots
  \]
  Wait: $\frac{p(w)}{\sqrt{1-p(w)}} = \frac{4w}{(1+w)(1-w)}$, and $\sqrt{1-p(w)} + \sqrt{1-p(v)} = \frac{1-w}{1+w} + \frac{1-v}{1+v} = \frac{2(1-wv)}{(1+w)(1+v)}$, so
  \[
  B(p(w), p(v)) = -\frac{1}{2} \frac{4w}{(1+w)(1-w)} \frac{4v}{(1+v)(1-v)} \frac{(1+w)^2(1+v)^2}{4(1-wv)^2} = -2 \frac{wv(1+w)(1+v)}{(1-w)(1-v)(1-wv)^2} \dots
  \]
  WAIT A SECOND! That has $\frac{1+w}{1-w}$! Why didn't $(1-w)(1-v)$ cancel?
  Because in $[w^0 v^0]\bigl(B(p(w), p(v)) \sum \sigma_m p(w)^{-m} \sum \sigma_n p(v)^{-n}\bigr)$, the Jacobian is $\frac{dp}{p} = \frac{1-w}{1+w} \frac{dw}{w}$!
  Indeed, by change of variable $p = p(w)$:
  \[
  \sum_{m=1}^\infty A_m \sigma_m = \oint \frac{dp}{2\pi i p} A(p) \sum_{m=1}^\infty \sigma_m p^{-m} = \oint \frac{dw}{2\pi i w} \frac{1-w}{1+w} A(p(w)) \sum_{m=1}^\infty \sigma_m p(w)^{-m}!
  \]
  NOW COMPUTE $\frac{1-w}{1+w} A(p(w))$ AND $\frac{1-w}{1+w}\frac{1-v}{1+v} B(p(w), p(v))$:
  - $\frac{1-w}{1+w} A(p(w)) = \frac{1-w}{1+w} \cdot \frac{-4iw}{1-w} = -\frac{4iw}{1+w} = -4i\sum_{n=1}^\infty (-1)^{n-1} w^n$!!
  - $\frac{1-w}{1+w}\frac{1-v}{1+v} B(p(w), p(v)) = -2 \frac{wv}{(1-wv)^2} = -2\sum_{n=1}^\infty n (wv)^n$!!
  THEREFORE:
  \[
  \sum_{m=1}^\infty A_m \sigma_m = -4i\sum_{n=1}^\infty (-1)^{n-1} t_n, \qquad
  \sum_{m,n=1}^\infty B_{m,n} \sigma_m \sigma_n = -2\sum_{n=1}^\infty n t_n^2!!
  \]
  EVERY SINGLE FACTOR AND SIGN MATCHES TO PERFECTION!

(3) Write $\Omega(x; z) = \Omega_+(x) + \Omega_-(x) - 1$ where $\Omega_+(x) = 1 + \sum_{m=1}^\infty a_m(z) x^m$ and $\Omega_-(x) = 1 + \sum_{m=1}^\infty a_m(z) (z/x)^m$. Define $\sigma_{*, m} := i \frac{a_m(z)}{m} z^m$, and let $f_*(x) := \sum_{m=1}^\infty \sigma_{*, m} x^{-m}$. Notice
\[
x \frac{d}{dx} f_*(x) = -i \sum_{m=1}^\infty a_m(z) (z/x)^m = -i\bigl(\Omega_-(x) - 1\bigr).
\]
Now substitute $x = p(w) = \frac{4w}{(1+w)^2}$ (which is invariant under $w \leftrightarrow w^{-1}$!). Because $\frac{dp}{p} = \frac{1-w}{1+w}\frac{dw}{w}$, we have
\[
w \frac{d}{dw} f_*(p(w)) = \frac{1-w}{1+w} \left(p \frac{d}{dp} f_*(p)\right) = -i \frac{1-w}{1+w}\bigl(\Omega_-(p(w)) - 1\bigr).
\]
On the other hand, look at the product $H(w) := \frac{1-w}{1+w} \Omega(p(w); z)$:
- Because $\frac{1-w}{1+w} = \sqrt{1 - p(w)}$ cancels the $\sqrt{1 - x}$ in the denominator of $\Omega(x; z)$,
  \[
  H(w) = \frac{1}{{}_2F_1(\frac{1}{2}, \frac{1}{2}; 1; z)\sqrt{1 - z/p(w)}}
  \]
  is **EVEN** under $w \leftrightarrow w^{-1}$ (since $p(w^{-1}) = p(w)$) and holomorphic on an annulus containing $|w| = 1$ (for small $|z|$)!
- Meanwhile, $\frac{1-w}{1+w}$ is **ODD** under $w \leftrightarrow w^{-1}$!
- Writing $\Omega(p(w); z) = \Omega_+(p(w)) + \bigl(\Omega_-(p(w)) - 1\bigr)$, we split $H(w)$ into its positive, constant, and negative powers of $w$:
  - $\frac{1-w}{1+w} \Omega_+(p(w)) = 1 + \sum_{n=1}^\infty c_n w^n$ has **only non-negative powers of $w$** (since $p(w) = 4w + O(w^2)$ and $\frac{1-w}{1+w} = 1 - 2w + \dots$ are holomorphic at $w = 0$)!
  - $\frac{1-w}{1+w}(\Omega_-(p(w)) - 1) = i w \frac{d}{dw} f_*(p(w)) = i \sum_{n \in \mathbb{Z}} n \hat f_n w^n$, where $\hat f_{-n} = t_{*, n}$ ($n \geq 1$) and by $w \leftrightarrow w^{-1}$ symmetry of $f_*(p(w))$, $\hat f_{+n} = \hat f_{-n} = t_{*, n}$!
  - Therefore $\frac{1-w}{1+w}(\Omega_-(p(w)) - 1) = i\sum_{n=1}^\infty n t_{*, n} (w^n - w^{-n})$ is **ODD** in $w \leftrightarrow w^{-1}$!
- Since $H(w) = \frac{1-w}{1+w}\Omega_+(p(w)) + i\sum_{n=1}^\infty n t_{*, n}(w^n - w^{-n})$ is **EVEN** under $w \leftrightarrow w^{-1}$, equating the negative-power coefficients $[w^{-n}] H(w) = [w^{+n}] H(w)$ ($n \geq 1$) gives:
  \[
  -i n t_{*, n} = c_n + i n t_{*, n} \implies c_n = -2i n t_{*, n} \qquad (\forall n \geq 1)!!
  \]
- Hence:
  \[
  \frac{1-w}{1+w} \Omega_+(p(w)) = 1 - 2i \sum_{n=1}^\infty n t_{*, n} w^n = 1 - g_*(w)!!
  \]
- Now verify the saddle-point equation $(I + M(z))\sigma_* = -\frac{1}{2} D^{-1} Z A$, i.e. $2 m z^{-m}\sigma_{*, m} + A_m + 2\sum_{n=1}^\infty B_{m,n}\sigma_{*, n} = 0$:
  Using $S^{(0)}(\sigma) = -4i\sum (-1)^{n-1} t_n - 2\sum n t_n^2$, we have
  \[
  \frac{\partial S^{(0)}}{\partial \sigma_m} = \sum_{n=1}^\infty \bigl(-4i(-1)^{n-1} - 4 n t_n\bigr) [w^{-n}] p(w)^{-m} = [w^0]\Bigl(p(w)^{-m} \bigl(-\tfrac{4iw}{1+w} - 4\sum_{n=1}^\infty n t_n w^n\bigr)\Bigr).
  \]
  At $\sigma = \sigma_*$, substitute $-2i\sum_{n \geq 1} n t_{*,n} w^n = \frac{1-w}{1+w}\Omega_+(p(w)) - 1$:
  \[
  -\frac{4iw}{1+w} - 4\sum_{n=1}^\infty n t_{*, n} w^n = -\frac{4iw}{1+w} + 2i\left(\frac{1-w}{1+w}\Omega_+(p(w)) - 1\right) = 2i\frac{1-w}{1+w}\bigl(\Omega_+(p(w)) - 1\bigr) - 2i.
  \]
  Pulling back $[w^0] p(w)^{-m}(\cdots) = \oint \frac{dw}{2\pi i w} p(w)^{-m}(\cdots) = \oint \frac{dp}{2\pi i p} \frac{1+w}{1-w} p^{-m}(\cdots)$:
  - The constant $-2i$ term has $\frac{1+w}{1-w} = (1-p)^{-1/2}$? Wait: $[w^0] p(w)^{-m} (-2i) = -2i [w^0] \frac{(1+w)^{2m}}{4^m w^m} = -2i \frac{1}{4^m}\binom{2m}{m} = A_m$! No, we want the FULL expression! Let's keep it in $w$:
  Notice $\frac{1-w}{1+w} \frac{dw}{w} = \frac{dp}{p}$, so
  \[
  \oint \frac{dw}{2\pi i w} p(w)^{-m} \cdot 2i\frac{1-w}{1+w} \Omega_+(p(w)) = 2i \oint \frac{dp}{2\pi i p} p^{-m} \Omega_+(p) = 2i a_m(z)!!
  \]
  Wait: what about the remaining term $-\frac{4iw}{1+w} - 2i = -2i\frac{1+3w}{1+w}$? Check!
  $-\frac{4iw}{1+w} - 2i = -2i \frac{1-w}{1+w} - 4i \frac{w}{1+w} - 2i \dots$ No! Combine $-\frac{4iw}{1+w} - 2i = -2i\frac{1 + 3w}{1+w}$? No: check the sign in $g(w) = 2i\sum n t_n w^n$:
  $-4\sum n t_n w^n = +2i g(w) = +2i\bigl(1 - \frac{1-w}{1+w}\Omega_+(p(w))\bigr)$!
  NOW add $-\frac{4iw}{1+w}$ to $+2i\bigl(1 - \frac{1-w}{1+w}\Omega_+(p(w))\bigr)$!!
  \[
  -\frac{4iw}{1+w} + 2i - 2i\frac{1-w}{1+w}\Omega_+(p(w)) = 2i\frac{1-w}{1+w}\bigl(1 - \Omega_+(p(w))\bigr)!!
  \]
  **EXACT CANCELLATION!!**
  Therefore, for every $m \geq 1$:
  \[
  \left.\frac{\partial S^{(0)}}{\partial \sigma_m}\right|_{\sigma_*} = \oint \frac{dw}{2\pi i w} p(w)^{-m} \cdot 2i\frac{1-w}{1+w}\bigl(1 - \Omega_+(p(w))\bigr) = 2i \oint \frac{dp}{2\pi i p} p^{-m}\bigl(1 - \Omega_+(p)\bigr) = -2i a_m(z) = -2m z^{-m} \sigma_{*, m}!!
  \]
  Since $\bar\sigma_{*, m} = -\sigma_{*, m}$, this is literally $-2m z^{-m}\bar\sigma_{*, m} + \partial_{\sigma_m} S^{(0)}(\sigma_*) = 0$! Hence $\sigma_{*, m} = i\frac{a_m(z)}{m} z^m$ is the **exact** saddle point!

- **Evaluation of $\mathcal{I}_0(z)$**: By the envelope theorem (stationarity of $\mathcal{I}_0 = -2\sum m z^{-m}\sigma_m\bar\sigma_m + S^{(0)}(\sigma) + \widetilde{S}^{(0)}(\bar\sigma)$ at $(\sigma_*, \bar\sigma_*)$):
  \[
  z \frac{d}{dz} \mathcal{I}_0(z) = 2 \sum_{m=1}^\infty m^2 z^{-m} \sigma_{*, m} \bar\sigma_{*, m} = 2\sum_{m=1}^\infty m^2 z^{-m} \left(\frac{a_m(z)}{m} z^m\right)^2 = 2\sum_{m=1}^\infty a_m(z)^2 z^m.
  \]
  On the other hand, $[x^0]\bigl(\Omega(x; z)^2\bigr) = 1 + 2\sum_{m=1}^\infty a_m(z)^2 z^m$, and directly from the definition of $\Omega(x; z)$:
  \[
  [x^0]\bigl(\Omega(x; z)^2\bigr) = \frac{1}{{}_2F_1(\frac{1}{2}, \frac{1}{2}; 1; z)^2} [x^0]\!\left(\frac{1}{(1-x)(1-z/x)}\right) = \frac{1}{\theta_3(q(z))^4 (1 - z)}!
  \]
  Hence $z \frac{d}{dz}\mathcal{I}_0(z) = \frac{1}{(1-z)\theta_3(q(z))^4} - 1 = z \frac{d}{dz}\log\frac{16 q(z)}{z}$. Since $\mathcal{I}_0(0) = 0$ and $\log\frac{16q(z)}{z}\big|_{z=0} = 0$, we obtain $\mathcal{I}_0(z) = \log\frac{16 q(z)}{z}$.

- **Evaluation of $1 - g_*(\pm 1)$**: From $1 - g_*(w) = \frac{1-w}{1+w}\Omega_+(p(w))$ and $H(w) = \frac{1-w}{1+w}\Omega(p(w); z) = (1 - g_*(w)) + i\sum_{n \geq 1} n t_{*,n}(w^n - w^{-n})$:
  Notice the second term vanishes identically at $w = \pm 1$ (since $w^n = w^{-n}$ for $w = \pm 1$)! Therefore:
  - At $w = 1$: $p(1) = 1$, so $1 - g_*(1) = H(1) = \frac{1}{{}_2F_1(\frac{1}{2},\frac{1}{2};1;z)\sqrt{1 - z}} = \frac{1}{\theta_3(q)^2 \cdot (\theta_4(q)/\theta_3(q))^2} = \theta_4(q)^{-2}$!
  - At $w = -1$: $p(-1) = \infty$, so $1 - g_*(-1) = H(-1) = \frac{1}{{}_2F_1(\frac{1}{2},\frac{1}{2};1;z)\sqrt{1 - 0}} = \theta_3(q)^{-2}$! $\square$

---

### Lemma A4 (Exact determinant $\det(I - M(z)^2)^{-1/2} = (1 - z)^{-1/8} \theta_3(q(z))^{-1}$)

**Claim.** As formal power series in $z$:
\[
\det\bigl(I - M(z)^2\bigr)^{-1/2} = (1 - z)^{-1/8} \, {}_2F_1\!\left(\tfrac{1}{2}, \tfrac{1}{2}; 1; z\right)^{-1/2} = (1 - z)^{-1/8} \theta_3\bigl(q(z)\bigr)^{-1}.
\]

**Proof.**
Fix $z \in \mathbb{C}$ with $|z|$ sufficiently small (say $|z| < 1/16$). Because $B(p, q)$ is holomorphic on $\{|p| < 1, |q| < 1\}$ (where $\operatorname{Re}\sqrt{1-p} > 0, \operatorname{Re}\sqrt{1-q} > 0$), Cauchy's inequality gives $|B_{m,n}| \leq C_\rho \rho^{-m-n}$ for every $0 < \rho < 1$. The symmetric matrix $\widetilde{M}(z)_{m,n} := \frac{z^{(m+n)/2}}{\sqrt{mn}} B_{m,n}$ (similar to $M(z)$) is trace-class with $\|\widetilde{M}(z)\|_{\mathrm{HS}} < 1/2$ for small $|z|$, so $K_{12} := (I - M_1 M_2)^{-1}$ and $K_{21} := (I - M_2 M_1)^{-1}$ (where $M_1 = D^{-1} B^{(z)}$, $M_2 = D^{-1} B$, $B^{(z)}_{m,n} = z^{m+n} B_{m,n}$) converge in operator norm, and the Fredholm determinant agrees with the formal series $\det(I - M(z)^2)$.

On the annulus $|z| < |x_1|, |x_2| < 1$, define the convergent Laurent series
\[
W_{\mathrm{no}}(x_1, x_2) := \sum_{m, n \geq 1} \Bigl(A_{++, mn} x_1^{-m-1} x_2^{-n-1} + A_{--, mn} x_1^{m-1} x_2^{n-1} + A_{-+, mn} x_1^{m-1} x_2^{-n-1} + A_{+-, mn} x_1^{-m-1} x_2^{n-1}\Bigr)
\]
with matrix blocks
\[
A_{++} = -B^{(z)} K_{21}, \qquad A_{--} = -B K_{12}, \qquad A_{-+} = B K_{12} M_1, \qquad A_{+-} = A_{-+}^T = B^{(z)} K_{21} M_2,
\]
and set $W(x_1, x_2) := \frac{1}{(x_1 - x_2)^2} + W_{\mathrm{no}}(x_1, x_2)$. (Here $B^T = B$, $(B^{(z)})^T = B^{(z)}$, $D M_1 = B^{(z)}$, $D M_2 = B$, and $K_{12}, K_{21}$ satisfy $D + B K_{12} M_1 = D K_{21}$, $B K_{12} = D K_{21} M_2$, $D + B^{(z)} K_{21} M_2 = D K_{12}$, and $B^{(z)} K_{21} = D K_{12} M_1$.)

1. **Rational twist identity.** Setting $s_1 = \sqrt{1-p}, s_2 = \sqrt{1-q}$ (so $p - q = s_2^2 - s_1^2$), direct algebra gives
   \[
   \sqrt{1 - p}\left(B(p, q) - \frac{pq}{(p-q)^2}\right) = -pq\left(\frac{1}{2 s_2(s_1+s_2)^2} + \frac{s_1}{(s_2^2-s_1^2)^2}\right) = -\frac{pq(s_1^2+s_2^2)}{2 s_2(s_2^2-s_1^2)^2} = -\frac{pq(2 - p - q)}{2\sqrt{1-q}\,(p - q)^2}.
   \]
   Expanding in $q$ for $|q| < |p|$ shows that every $[q^n]$-coefficient has only non-positive powers of $p$ (a polynomial in $x = 1/p$ of degree $n$). Equivalently, for every $n \geq 1$,
   \[
   f_n(x) := \sum_{m=1}^\infty B_{m,n} x^{-m-1} - n x^{n-1}
   \]
   has the property that $P_n(x) := \sqrt{x(x-1)} f_n(x)$ is a **polynomial in $x$ of degree $n$**.

2. **Analytic continuation to $\mathbb{P}^1$ and Liouville's theorem.** Fix $x_2$ with $|z| < |x_2| < 1$.
   - For $|z| < |x_1| < |x_2|$: expanding $\frac{1}{(x_1-x_2)^2} = \sum_{m \geq 1} m x_1^{m-1} x_2^{-m-1}$ adds $+D x_2^{-\bullet - 1}$ to the positive powers of $x_1$. Using $D + B K_{12} M_1 = D K_{21}$ and $B K_{12} = D K_{21} M_2$, setting $v(x_2) := K_{21}(x_2^{-\bullet-1} - M_2 x_2^{\bullet-1})$ yields
     \[
     W(x_1, x_2) = -\sum_{n=1}^\infty v_n(x_2) z^{n-1} f_n(x_1/z),
     \]
     so $\sqrt{x_1(x_1-z)} W(x_1, x_2) = -\sum_{n=1}^\infty v_n(x_2) z^n P_n(x_1/z)$ has only non-negative powers of $x_1$ and extends holomorphically to the entire disc $|x_1| < |x_2|$.
   - For $|x_2| < |x_1| < 1$: expanding $\frac{1}{(x_1-x_2)^2} = \sum_{m \geq 1} m x_1^{-m-1} x_2^{m-1}$ and setting $w(x_2) := K_{12}(x_2^{\bullet-1} - M_1 x_2^{-\bullet-1})$ yields
     \[
     W(x_1, x_2) = -\frac{1}{x_1^2}\sum_{n=1}^\infty w_n(x_2) f_n(1/x_1),
     \]
     so $x_1\sqrt{x_1 - 1}\, W(x_1, x_2) = i\sum_{n=1}^\infty w_n(x_2) P_n(1/x_1)$ has only non-positive powers of $x_1$ and extends holomorphically to the entire exterior disc $|x_1| > |x_2|$ including $x_1 = \infty$.
   - Multiplying by $Y(x_1) := \sqrt{x_1(x_1 - z)(x_1 - 1)}$ (choosing the branch $Y(x) \sim x^{3/2}$ as $x \to \infty$, so $Y(x) = i x \sqrt{1-z/x}\sqrt{1-x}$ on the annulus $|z| < |x| < 1$), the product $Y(x_1) W(x_1, x_2)$ extends to a single-valued meromorphic function on $\mathbb{P}^1$, holomorphic at $\infty$, with its only singularity a double pole at $x_1 = x_2$ of principal part $Y(x_1)/(x_1-x_2)^2$.
   - Since $W(x_1, x_2) = W(x_2, x_1)$ and the symmetric polynomial $S(x_1, x_2) := \frac{1}{2}[x_1 x_2(x_1+x_2) - 2(1+z)x_1 x_2 + z(x_1+x_2)]$ satisfies $S(x, x) = Y(x)^2$, $\partial_{x_1} S(x, x) = Y(x) Y'(x)$, and $\deg_{x_1} S = 2$, Liouville's theorem on $\mathbb{P}^1$ uniquely forces
     \[
     W(x_1, x_2) = \frac{S(x_1, x_2)}{Y(x_1) Y(x_2) (x_1 - x_2)^2} + \frac{2 C(z)}{Y(x_1) Y(x_2)}
     \]
     for a scalar function $C(z)$ independent of $(x_1, x_2)$.

3. **Zero-mode condition fixes $C(z)$.** On the annulus $|z| < |x_1| < 1$, $W(x_1, x_2)$ has no $x_1^{-1}$ term, so $\oint_{|x_1|=r} W(x_1, x_2) \frac{dx_1}{2\pi i} = 0$. Taking the $x_2^{-3/2}$ asymptotics as $x_2 \to \infty$ (where $S(x_1, x_2)/(x_1-x_2)^2 \to x_1/2$ and $Y(x_2) \sim x_2^{3/2}$) gives
   \[
   \oint_{|x_1|=r} \frac{x_1/2 + 2 C(z)}{Y(x_1)} \frac{dx_1}{2\pi i} = 0 \implies 2 C(z) = -\frac{1}{2} \frac{I_1(z)}{I_0(z)},
   \]
   where $I_0(z) = [x^0](1-z/x)^{-1/2}(1-x)^{-1/2} = \sum_{n=0}^\infty \binom{-1/2}{n}^2 z^n = {}_2F_1(\frac{1}{2}, \frac{1}{2}; 1; z)$ and $I_1(z) = [x^{-1}](1-z/x)^{-1/2}(1-x)^{-1/2} = \sum_{n=0}^\infty \binom{-1/2}{n}^2 \frac{n+1/2}{n+1} z^{n+1}$. Since $[z^{n+1}] z(1-z) I_0'(z) = \frac{1}{4(n+1)}\binom{-1/2}{n}^2$, we have the exact identity $I_1(z) = z I_0(z) - 2 z(1-z) I_0'(z)$, hence
   \[
   2 C(z) = -\frac{z}{2} + z(1-z)\frac{I_0'(z)}{I_0(z)}.
   \]

4. **Logarithmic derivative via Cauchy's residue theorem.** On the annulus $|z| < |x| < 1$, expanding $W_{\mathrm{no}}(x, x)$ at $x_1 = x_2 = x$ shows that the only terms contributing to $[x^{-2}] W_{\mathrm{no}}(x, x)$ are the diagonal entries of $A_{-+}$ and $A_{+-}$:
   \[
   \oint_{|x|=r} \frac{x}{2} W_{\mathrm{no}}(x, x) \frac{dx}{2\pi i} = \operatorname{Tr}\bigl(B K_{12} M_1\bigr) = \operatorname{Tr}\bigl(D M_2 (I - M_1 M_2)^{-1} M_1\bigr) = \operatorname{Tr}\bigl(D M(z)^2 (I - M(z)^2)^{-1}\bigr).
   \]
   Because $z\frac{d}{dz} M(z) = D M(z)$, we have $z\frac{d}{dz}\log\det(I - M(z)^2)^{-1/2} = \operatorname{Tr}(D M(z)^2(I - M(z)^2)^{-1})$. On the other hand, taking the coincidence limit $x_1 \to x$ of $W(x_1, x) - \frac{1}{(x_1-x)^2}$ gives the rational function
   \[
   W_{\mathrm{no}}(x, x) = \frac{(x^2 - z)^2}{8 x^2 (x-1)^2 (x-z)^2} + \frac{2 C(z)}{x(x-1)(x-z)}.
   \]
   Computing the residues at the two poles $x = 0, z$ inside $|x| = r$ yields
   \[
   \operatorname{Res}_{x=0, z}\left(\frac{x}{2} W_{\mathrm{no}}(x, x)\right) = \frac{z}{8(z - 1)} + \frac{2 C(z)}{2(z - 1)} = \frac{z}{8(z - 1)} + \frac{-\frac{z}{2} + z(1-z)\frac{I_0'(z)}{I_0(z)}}{2(z-1)} = \frac{z}{8(1 - z)} - \frac{1}{2} z \frac{I_0'(z)}{I_0(z)}.
   \]
   Integrating $z\frac{d}{dz}\log\det(I - M(z)^2)^{-1/2} = z\frac{d}{dz}\log\bigl((1-z)^{-1/8} I_0(z)^{-1/2}\bigr)$ from $z = 0$ (where both sides equal $1$) yields $\det(I - M(z)^2)^{-1/2} = (1-z)^{-1/8} I_0(z)^{-1/2} = (1-z)^{-1/8}\theta_3(q(z))^{-1}$. $\square$

---

### Lemma A5 (Exact external-weight exponents $\Phi_1, \Phi_2$)

**Claim.** $S^{(2)}_2(\sigma) = 2\log(1 - g(1))$ and $S^{(2)}_1(\sigma) = 2\log(1 - g(-1))$, hence
\[
\Phi_2(z) = -4\log\theta_4(q(z)), \qquad \Phi_1(z) = -4\log\theta_3(q(z)).
\]

**Proof.**
Recall $g(w) = 2i\sum_{n=1}^\infty n t_n w^n = 2i\sum_{m=1}^\infty \sigma_m \sum_{n=1}^m 4^{-m} n \binom{2m}{m-n} w^n$. At $w = \pm 1$:
- Using $n\binom{2m}{m-n} = m\bigl(\binom{2m-1}{m-n} - \binom{2m-1}{m-n-1}\bigr)$, the sum at $w = 1$ telescopes to $\sum_{n=1}^m n\binom{2m}{m-n} = m\binom{2m-1}{m-1} = \frac{m}{2}\binom{2m}{m}$. Hence $g(1) = \sum_{m=1}^\infty c^+_m \sigma_m$ has generating function
  \[
  C_+(p) := \sum_{m=1}^\infty c^+_m p^m = i p \frac{d}{dp}(1-p)^{-1/2} = \frac{i}{2} p(1-p)^{-3/2}.
  \]
- At $w = -1$, similarly $\sum_{n=1}^m (-1)^n n\binom{2m}{m-n} = -\binom{2m-2}{m-1}$ (checked by comparing coefficients of $p^m$ in $\frac{1-w}{1+w} \cdot 2i w\frac{d}{dw}\frac{1}{1+w}\big|_{w=-1}$ or telescoping $(-1)^n\binom{2m-1}{m-n}$: $\sum_{n=1}^m (-1)^n\bigl(\binom{2m-1}{m-n} - \binom{2m-1}{m-n-1}\bigr)$ — wait: let's prove $\sum_{n=1}^m (-1)^n n\binom{2m}{m-n} = -\binom{2m-2}{m-1}$ directly by one line: $\sum_{j=0}^{m-1} (-1)^{m-j} (m-j)\binom{2m}{j} = [x^{m-1}] \frac{1}{(1+x)^2} (1-x)^{2m}$? Even simpler: check $\Delta_n\bigl[(-1)^{n-1} \frac{n(n+1)}{2} \cdots\bigr]$ — NO, use $(1-w)^{2m}$ directly:
  $g(-1) = 2i\sum_{n=1}^\infty (-1)^n n t_n = 2i [w^0] \Bigl(\sum_{n=1}^\infty (-1)^n n w^n \cdot \sum_{m=1}^\infty \sigma_m p(w)^{-m}\Bigr) = -2i \oint \frac{dw}{2\pi i w} \frac{w}{(1+w)^2} \sum_{m=1}^\infty \sigma_m p(w)^{-m}$.
  NOW SUBSTITUTE $p = p(w) = \frac{4w}{(1+w)^2}$ and $\frac{dw}{w} = \frac{1+w}{1-w}\frac{dp}{p} = (1-p)^{-1/2}\frac{dp}{p}$!!
  \[
  g(-1) = -2i \oint \frac{dp}{2\pi i p} (1-p)^{-1/2} \cdot \frac{p}{4} \sum_{m=1}^\infty \sigma_m p^{-m} = -\frac{i}{2} \sum_{m=1}^\infty \sigma_m [p^m]\bigl(p(1-p)^{-1/2}\bigr)!!
  \]
  **ONE LINE!! ZERO BINOMIAL GYMNASTICS!!**
  And the exact same 1-line contour integral gives $g(1)$:
  $\sum_{n=1}^\infty n w^n = \frac{w}{(1-w)^2} = \frac{w}{(1+w)^2} \cdot \left(\frac{1+w}{1-w}\right)^2 = \frac{p}{4} (1-p)^{-1}$, so
  \[
  g(1) = 2i \oint \frac{dp}{2\pi i p} (1-p)^{-1/2} \cdot \frac{p}{4}(1-p)^{-1} \sum_{m=1}^\infty \sigma_m p^{-m} = +\frac{i}{2} \sum_{m=1}^\infty \sigma_m [p^m]\bigl(p(1-p)^{-3/2}\bigr)!!
  \]
  Thus $C_+(p) = \frac{i}{2} p(1-p)^{-3/2}$ and $C_-(p) = -\frac{i}{2} p(1-p)^{-1/2}$!)

Now since $L_k^{(0)}$ is a first-order derivation, $L_k^{(0)}\bigl(2\log(1 - g(\pm 1))\bigr) = -2 \frac{L_k^{(0)} g(\pm 1)}{1 - g(\pm 1)}$, so $L_k^{(0)} S^{(2)}_2 = k$ and $L_k^{(0)} S^{(2)}_1 = -1$ reduce to the linear identities
\[
L_k^{(0)} g(1) = -\frac{k}{2}(1 - g(1)), \qquad L_k^{(0)} g(-1) = +\frac{1}{2}(1 - g(-1)) \qquad (\forall k \geq 1).
\]
In terms of $s_1 = \sqrt{1-p}$ and $s_2 = \sqrt{1-q}$ (so $A(p) = -2i(s_1^{-1}-1)$, $C_+(p) = \frac{i}{2}\frac{1-s_1^2}{s_1^3}$, $C_-(p) = -\frac{i}{2}\frac{1-s_1^2}{s_1}$):
- Constant term in $\sigma$: $\sum_{k=1}^\infty [L_k^{(0)} g(\pm 1)]_{\sigma^0} p^k = (i - \frac{1}{2} A(p)) C_\pm(p) = \frac{i}{s_1} C_\pm(p)$, which gives $-\frac{1-s_1^2}{2 s_1^4} = -\frac{p}{2(1-p)^2} = \sum_{k \geq 1}(-\frac{k}{2})p^k$ for $g(1)$ and $+\frac{1-s_1^2}{2 s_1^2} = +\frac{p}{2(1-p)} = \sum_{k \geq 1}(+\frac{1}{2})p^k$ for $g(-1)$.
- Linear term in $\sigma$: $\sum_{k,m \geq 1} [L_k^{(0)} g(\pm 1)]_{\sigma_m} p^k q^m = q\partial_q\bigl(\frac{p C_\pm(q) - q C_\pm(p)}{q-p} - \frac{p}{1-p} C_\pm(q)\bigr) - B(p, q) C_\pm(p)$. Setting $p = 1-s_1^2, q = 1-s_2^2$ reduces this directly to $+\frac{p}{2(1-p)^2} C_+(q)$ for $g(1)$ and $-\frac{p}{2(1-p)} C_-(q)$ for $g(-1)$ (both pure rational identities in $(s_1, s_2)$).

By uniqueness of $S^{(2)}_1, S^{(2)}_2$ (Lemma A2), $S^{(2)}_2 = 2\log(1 - g(1))$ and $S^{(2)}_1 = 2\log(1 - g(-1))$. Evaluating at $\sigma_*$ via Lemma A3(3) gives $\Phi_2(z) = 2\log(\theta_4(q)^{-2}) = -4\log\theta_4(q)$ and $\Phi_1(z) = 2\log(\theta_3(q)^{-2}) = -4\log\theta_3(q)$. $\square$

---

### Lemma A6 (Exact central-charge exponent $\Phi_c^{\mathrm{raw}}(z)$ via $c = 1 + 1 = 2$)

**Claim.**
\[
\exp\bigl(\Phi_c^{\mathrm{raw}}(z) - \mathcal{I}_0(z)\bigr) = \prod_{m=1}^\infty (1 - q(z)^{2m})^{12} = \frac{z}{16 q(z)}(1 - z)\theta_3(q(z))^{12}.
\]

**Proof.**
Consider the tensor product $\mathcal{H}_\lambda := \mathcal{F}_{0, \lambda}^{(1)} \otimes \mathcal{F}_{0, 0}^{(2)}$ of two $c = 1$ unitary Fock modules (oscillators $v_m$ of weight $\Delta = \lambda^2$ with $\lambda > 0$, and $u_m$ of weight $0$), carrying the diagonal unitary $c = 2$ Virasoro representation $L_k^{\mathrm{tot}} = l_k^{(1)} + l_k^{(2)}$.

1. **Exact $c = 1 + 1 = 2$ block decomposition.** At $\mu = 0$ and $\Delta_1 = \Delta_2 = \frac{1}{16}$, Lemma A2(2) shows that the exact finite-$\lambda$ Ward identity $l_k F = (l_0 + \frac{k-1}{16}) F$ is solved identically by the pure Gaussians
   \[
   F_1(v) = \exp\Bigl(\lambda \sum_{m=1}^\infty A_m v_m + \sum_{m,n=1}^\infty B_{m,n} v_m v_n\Bigr), \qquad F_2(u) = \exp\Bigl(\sum_{m,n=1}^\infty B_{m,n} u_m u_n\Bigr),
   \]
   whose pairings are $\mathcal{B}(1, \lambda^2, \frac{1}{16}; z) = \det(I - M(z)^2)^{-1/2} (16 q(z)/z)^{\lambda^2}$ and $\mathcal{B}(1, 0, \frac{1}{16}; z) = \det(I - M(z)^2)^{-1/2}$ (Lemmas A2–A4). Their tensor product $F_{\mathrm{tot}}(v, u) := F_1(v) F_2(u)$ satisfies the exact $c = 2$, $\Delta_1 = \Delta_2 = \frac{1}{8}$ Ward identity $L_k^{\mathrm{tot}} F_{\mathrm{tot}} = (L_0^{\mathrm{tot}} + \frac{k-1}{8}) F_{\mathrm{tot}}$.

   Since $c = 2 > 1$ and $\lambda^2 + n > 0$ for all $n \geq 0$, every Verma module $V(2, \lambda^2 + n)$ is irreducible and unitary (Lemma A1(1)). Because $\mathcal{H}_\lambda$ is unitary with weight-space dimensions $\sum_{k=0}^N p(k) p(N-k)$, it decomposes orthogonally into Virasoro Verma modules
   \[
   \mathcal{H}_\lambda = \bigoplus_{n=0}^\infty \bigoplus_{j=1}^{p(n)} V_{2, \lambda^2 + n}^{(j)},
   \]
   where the space $\mathcal{P}_n(\lambda) := \{P \in (\mathcal{H}_\lambda)_n : L_k^{\mathrm{tot}} P = 0 \;\forall k \geq 1\}$ of primaries at level $n$ has dimension $p(n)$. Projecting $F_{\mathrm{tot}}(z^\bullet v, z^\bullet u)$ orthogonally onto each summand yields, as an exact identity of formal power series in $z$:
   \[
   \mathcal{B}(1, \lambda^2, \tfrac{1}{16}; z)\,\mathcal{B}(1, 0, \tfrac{1}{16}; z) = \sum_{n=0}^\infty c_n(\lambda^2)\, z^n \, \mathcal{B}(2, \lambda^2 + n, \tfrac{1}{8}; z),
   \]
   where $c_n(\lambda^2) = \sum_{a, b} \overline{\langle P_a, F_1 F_2 \rangle} (G^{(n)}(\lambda)^{-1})_{a, b} \langle P_b, F_1 F_2 \rangle$ for any basis $\{P_a\}$ of $\mathcal{P}_n(\lambda)$ with Gram matrix $G^{(n)}(\lambda)_{a,b} = \langle P_a, P_b \rangle$.

2. **Large-$\lambda$ primary basis and Virasoro diffeomorphism.** Rescaling $v_m = i\lambda W_m$ (so $l_k^{(1)} = D_k + \frac{1}{4\lambda^2}\sum_{r=1}^{k-1}\partial_{W_r}\partial_{W_{k-r}}$ with $D_k := \partial_{W_k} + \sum_{m=1}^\infty m W_m \partial_{W_{m+k}}$), for every $w(u) \in \mathcal{F}^{(2)}_n$ there is a unique primary $P_w(i\lambda W, u; \lambda) \in \mathcal{P}_n(\lambda)$ with $P_w(0, u; \lambda) = w(u)$, and by the exact same lowest-degree injectivity of $(D_1, \dots, D_r)$ as in Lemma A2(1), $P_w(i\lambda W, u; \lambda) = U(W) w(u) + O(\lambda^{-2})$, where $U(W) : \mathcal{F}^{(2)} \to \mathcal{F}^{(2)}[[W]]$ is the unique operator satisfying
   \[
   \bigl(D_k + l_k^{(2)}\bigr) U(W) = 0 \quad (\forall k \geq 1), \qquad U(0) = \mathrm{id}.
   \]
   Because every $v$-dependent term in $P_w(v, u; \lambda) = U(-i\lambda^{-1} v) w(u) + O(\lambda^{-2})$ carries a factor of $\lambda^{-1}$ per $v_m$, the Gram matrix satisfies $G^{(n)}(\lambda)_{w_1, w_2} = \langle w_1, w_2 \rangle_{\mathcal{F}^{(2)}} + O(\lambda^{-2})$. Meanwhile, pairing $\overline{v_m}$ with $F_1(v) = \exp(\lambda\sum A_m v_m + \sum B_{m,n} v_m v_n)$ replaces each $\overline{v_m}/\lambda$ by $\frac{A_m}{2m} + O(\lambda^{-2})$, i.e. $W_m = i\overline{v_m}/\lambda$ by $W_{*, m} := \frac{i A_m}{2m} = \frac{1}{m \cdot 4^m}\binom{2m}{m}$. Thus
   \[
   \lim_{\lambda \to \infty} \langle P_w, F_1 F_2 \rangle = \langle U(W_*) w, F_2 \rangle_{\mathcal{F}^{(2)}} = \langle w, U(W_*)^\dagger F_2 \rangle_{\mathcal{F}^{(2)}},
   \]
   and therefore
   \[
   c_n^\infty := \lim_{\lambda \to \infty} c_n(\lambda^2) = \left\| \bigl(U(W_*)^\dagger F_2\bigr)_n \right\|_{\mathcal{F}^{(2)}}^2.
   \]

3. **Exact evaluation of $U(W_*)^\dagger F_2$.** Taking the adjoint of $D_k U(W) = -l_k^{(2)} U(W)$ gives $D_k(U(W)^\dagger) = -U(W)^\dagger l_{-k}^{(2)}$ ($U(0)^\dagger = \mathrm{id}$). Define the Heisenberg current $\alpha(x) := \sum_{n \neq 0} \alpha_n x^{-n-1}$ on $\mathcal{F}^{(2)}$ with $\alpha_n = \frac{i}{\sqrt{2}}\partial_{u_n}$ and $\alpha_{-n} = -i\sqrt{2} n u_n$ ($n \geq 1$), satisfying $[l_{-k}^{(2)}, \alpha(x)] = \frac{d}{dx}(x^{1-k}\alpha(x))$. Then $\Phi(W, x) := U(W)^\dagger \alpha(x) (U(W)^\dagger)^{-1}$ satisfies
   \[
   D_k \Phi(W, x) = -\frac{d}{dx}\bigl(x^{1-k} \Phi(W, x)\bigr), \qquad \Phi(0, x) = \alpha(x).
   \]
   On the other hand, $f(x; W) := x \exp(-\sum_{m=1}^\infty W_m x^{-m})$ satisfies $D_k(f(x; W)) = -x^{1-k} f'(x; W)$ (since $D_k(\sum W_m x^{-m}) = x^{-k}(1 + \sum m W_m x^{-m}) = x^{1-k} f'(x)/f(x)$), so $f'(x; W)\alpha(f(x; W))$ solves the identical PDE with the same initial condition at $W = 0$. By uniqueness (injectivity of $D_k$), $U(W)^\dagger \alpha(x) (U(W)^\dagger)^{-1} = f'(x; W)\alpha(f(x; W))$.

   At $W = W_*$, since $\sum_{m=1}^\infty \frac{1}{m\cdot 4^m}\binom{2m}{m} y^m = \int_0^y \frac{(1-t)^{-1/2}-1}{t} dt = \log\frac{4(1-\sqrt{1-y})}{y(1+\sqrt{1-y})}$, we have
   \[
   X = f(x; W_*) = \frac{1 + \sqrt{1 - 1/x}}{4(1 - \sqrt{1 - 1/x})} \iff x = x(X) = X + \frac{1}{2} + \frac{1}{16 X},
   \]
   and $\sqrt{x(x-1)} = X - \frac{1}{16 X}$. By the rational twist identity of Lemma A4(1), $\sqrt{x(x-1)}\alpha(x) F_2(u)$ has only non-negative powers of $x$, i.e. $\oint x^{k-1}\sqrt{x(x-1)}\alpha(x)\,dx \cdot F_2 = 0$ for all $k \geq 1$. Applying $U(W_*)^\dagger$ and changing variables to $X = f(x; W_*)$ gives
   \[
   \oint x(X)^{k-1}\left(X - \frac{1}{16 X}\right) \alpha(X)\,dX \cdot \bigl(U(W_*)^\dagger F_2\bigr) = 0 \qquad (\forall k \geq 1).
   \]
   Because $x(X)$ is invariant under $X \mapsto \frac{1}{16 X}$ with leading term $X$, we have $\operatorname{span}_{k \geq 1}\{x(X)^{k-1}(X - \frac{1}{16 X})\} = \operatorname{span}_{m \geq 1}\{X^m - 16^{-m} X^{-m}\}$. Therefore $(\alpha_m - 16^{-m}\alpha_{-m})(U(W_*)^\dagger F_2) = 0$, i.e. $\partial_{u_m}(U(W_*)^\dagger F_2) = -\frac{2m}{16^m} u_m (U(W_*)^\dagger F_2)$ for all $m \geq 1$. Since $U(W_*)^\dagger = \mathrm{id} + (\text{level-raising})$ fixes the constant term $F_2(0) = 1$, we obtain
   \[
   U(W_*)^\dagger F_2(u) = \exp\Bigl(-\sum_{m=1}^\infty \frac{m}{16^m} u_m^2\Bigr).
   \]
   Taking its level-$n$ Fock norm squared (using $\langle \bar u_m^{2k}, u_m^{2k} \rangle = \frac{(2k)!}{(2m)^{2k}}$) yields
   \[
   \sum_{n=0}^\infty 16^n c_n^\infty q^n = \prod_{m=1}^\infty \sum_{k=0}^\infty \frac{m^{2k} (2k)!}{(k!)^2 (2m)^{2k}} q^{2mk} = \prod_{m=1}^\infty \sum_{k=0}^\infty \binom{-1/2}{k}(-q^{2m})^k = \prod_{m=1}^\infty (1 - q^{2m})^{-1/2}.
   \]

4. **Matching both sides of the $c = 1 + 1 = 2$ identity.** Divide the exact decomposition $\mathcal{B}(1, \lambda^2, \frac{1}{16}; z)\mathcal{B}(1, 0, \frac{1}{16}; z) = \sum_{n=0}^\infty c_n(\lambda^2) z^n \mathcal{B}(2, \lambda^2+n, \frac{1}{8}; z)$ by $(16q/z)^{\lambda^2}$ and take $\lambda \to \infty$ coefficient-by-coefficient in $z$ (at order $z^N$, the sum over $n$ is finite, $0 \leq n \leq N$!). Using Lemmas A2–A5 (noting that at $c = 2$, $\mu^2 = \frac{1}{24}$, $\Delta = \lambda^2 + n = (\lambda^2 + n - \frac{1}{24}) + \frac{1}{24}$, and $\Delta_j - \frac{1}{16} = \frac{1}{16}$):
   - LHS limit: $\bigl((1-z)^{-1/8}\theta_3(q)^{-1}\bigr)^2 = (1-z)^{-1/4}\theta_3(q)^{-2}$.
   - RHS limit: $\Bigl(\sum_{n=0}^\infty c_n^\infty (16q)^n\Bigr) \cdot (16q/z)^{-\frac{1}{24}} \cdot (1-z)^{-1/8}\theta_3(q)^{-1} \exp\bigl(\frac{1}{24}\Phi_c^{\mathrm{raw}}(z) + \frac{1}{8}\Phi_1(z) + \frac{1}{8}\Phi_2(z)\bigr)$.
   Since $\frac{1}{8}(\Phi_1 + \Phi_2) = -\frac{1}{2}\log(\theta_3\theta_4) = -\frac{1}{8}\log(1-z) - \log\theta_3$, the factor $(1-z)^{-1/4}\theta_3^{-2}$ cancels identically on both sides, leaving
   \[
   \exp\Bigl(\frac{1}{24}\bigl(\Phi_c^{\mathrm{raw}}(z) - \mathcal{I}_0(z)\bigr)\Bigr) = \prod_{m=1}^\infty (1 - q(z)^{2m})^{1/2}.
   \]
   Raising to the $24$-th power and applying Jacobi's identity $16 q \prod_{m=1}^\infty (1 - q^{2m})^{12} = (\theta_2\theta_3\theta_4)^4 = z(1-z)\theta_3^{12}$ gives the claim. $\square$

---

### Proof of Theorem S1A

Combine Lemmas A2–A6: for any $\mu > 0$ ($c = 1 + 24\mu^2$) and $\Delta_1, \dots, \Delta_4 \in \mathbb{R}$, writing $\Delta = \lambda^2 + \mu^2$ (so $(16q/z)^\Delta = e^{(\lambda^2 + \mu^2)\mathcal{I}_0(z)}$) and substituting $\theta_4^4 = (1-z)\theta_3^4$:
\begin{align*}
\lim_{\Delta \to \infty} \left(\frac{16q}{z}\right)^{-\Delta} \mathcal{B}(c, \Delta, \Delta_i; z)
&= (1-z)^{-1/8}\theta_3^{-1} \cdot \left(\frac{z}{16q}(1-z)\theta_3^{12}\right)^{\frac{c-1}{24}} \cdot \theta_3^{-4(\Delta_1+\Delta_4-\frac{1}{8})} \cdot \theta_4^{-4(\Delta_2+\Delta_3-\frac{1}{8})} \\
&= \left(\frac{16q}{z}\right)^{-\frac{c-1}{24}} (1-z)^{\frac{c-1}{24} - \Delta_2 - \Delta_3} \theta_3^{\frac{c-1}{2} - 4(\Delta_1+\Delta_2+\Delta_3+\Delta_4)} \\
&= z^{-(\Delta - \Delta_1 - \Delta_2)} \left(\frac{16q}{z}\right)^{-\Delta} \Phi(c, \Delta, \Delta_i; q(z)).
\end{align*}
Therefore $\lim_{\Delta \to \infty} H(c, \Delta, \Delta_i; q) = \lim_{\Delta \to \infty} \Phi^{-1} z^{\Delta - \Delta_1 - \Delta_2} \mathcal{B}(c, \Delta, \Delta_i; z) = 1$ in $\mathbb{C}[[q]]$, i.e., $\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_i) = \delta_{N, 0}$ for every $N \geq 0$. By Lemma A1(4), the same holds for all $(c, \Delta_1, \dots, \Delta_4) \in \mathbb{C}^5$. $\square$
