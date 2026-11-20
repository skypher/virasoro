# S1_CONF: Generic Zamolodchikov Recursion and Fixed-$b_\star$ All-Order Confluence

## 1. Conventions and Generic Residue Data

Throughout, $c(b) = 1 + 6(b + b^{-1})^2$, $Q(b) = b + b^{-1}$, and $h_{r,s}(b) = \frac{Q(b)^2 - (rb + sb^{-1})^2}{4}$ for $r, s \in \mathbb{Z}_{>0}$. External weights $\Delta_j$ ($j = 1, 2, 3, 4$) are parameterized via $\Lambda_j^2 = Q(b)^2 - 4\Delta_j$. The elliptic $H$-series is expanded in powers of $16 q$:
\[
H(c, \Delta, \Delta_i; q) = \sum_{N=0}^\infty H_N(c, \Delta, \Delta_i) (16 q)^N = \Phi(c, \Delta, \Delta_i; q)^{-1} z(q)^{\Delta - \Delta_1 - \Delta_2} \mathcal{B}(c, \Delta, \Delta_i; z(q)),
\]
where $\Phi(c, \Delta, \Delta_i; q) = (16 q)^{\Delta - \frac{c-1}{24}} z(q)^{\frac{c-1}{24} - \Delta_1 - \Delta_2} (1 - z(q))^{\frac{c-1}{24} - \Delta_2 - \Delta_3} \theta_3(q)^{\frac{c-1}{2} - 4(\Delta_1 + \Delta_2 + \Delta_3 + \Delta_4)}$.

**Definition 1 (Sphere generic residue data).** For $r, s \in \mathbb{Z}_{>0}$ and indeterminate external weights $\Delta_a, \Delta_b$, define the Zamolodchikov inverse norm derivative and sphere fusion polynomial:
\begin{align*}
\mathcal{A}_{r,s}(b) &:= \frac{1}{2} \prod_{\substack{1-r \leq p \leq r,\; 1-s \leq q \leq s \\ (p,q) \neq (0,0),\, (r,s)}} (p b + q b^{-1})^{-1}, \\
P_{r,s}(b, \Delta_a, \Delta_b) &:= \prod_{\substack{j = 1-r \\ j \equiv r-1 \pmod 2}}^{r-1} \prod_{\substack{l = 1-s \\ l \equiv s-1 \pmod 2}}^{s-1} \frac{\Lambda_a + \Lambda_b + j b + l b^{-1}}{2} \cdot \frac{\Lambda_a - \Lambda_b + j b + l b^{-1}}{2}.
\end{align*}
Notice that pairing $(j, l)$ with $(-j, -l)$ makes $P_{r,s}(b, \Delta_a, \Delta_b)$ symmetric in $\Lambda_a \mapsto -\Lambda_a$ and $\Lambda_b \mapsto -\Lambda_b$, hence a polynomial in $\mathbb{Q}[b, b^{-1}, \Delta_a, \Delta_b]$ of total degree $rs$ in $(\Delta_a, \Delta_b)$ (and symmetric in $(\Delta_a, \Delta_b)$ when $rs$ is even, or transforming by $(-1)^{rs}$ under $\Delta_a \leftrightarrow \Delta_b$? Let's check: under $\Lambda_a \leftrightarrow \Lambda_b$, $(\Lambda_a - \Lambda_b + j b + l b^{-1}) \mapsto -(\Lambda_a - \Lambda_b - j b - l b^{-1})$, so pairing $(j,l)$ with $(-j,-l)$ multiplies the product by $(-1)^{rs}$, matching $\gamma_{(1^{rs})}(\Delta; \Delta_a, \Delta_b) \sim (\Delta_b - \Delta_a)^{rs}$!). Define
\[
\mathcal{R}^{\mathrm{sph}}_{r,s}(b, \Delta_1, \Delta_2, \Delta_3, \Delta_4) := \mathcal{A}_{r,s}(b)\, P_{r,s}(b, \Delta_4, \Delta_3)\, P_{r,s}(b, \Delta_1, \Delta_2).
\]
*(Convention check: in `sphere/tools/exact_sphere_block.py`, $\langle \chi_{r,s}(b) | \Phi_2(1) | \Delta_1 \rangle = +P_{r,s}(b, \Delta_1, \Delta_2)$ was verified symbolically for all $rs \leq 4$ with $+1$ sign, where $P_{r,s}(b, \Delta_1, \Delta_2) = \prod (\frac{\Lambda_1 + \Lambda_2 + j b + l b^{-1}}{2})(\frac{\Lambda_1 - \Lambda_2 + j b + l b^{-1}}{2})$ has leading term $(-\Delta_1 + \Delta_2)^{rs}$ as $\Delta_2 - \Delta_1 \to \infty$! Check: at $(r,s)=(1,1)$, $j=l=0$, $P_{1,1} = \frac{\Lambda_1^2 - \Lambda_2^2}{4} = \Delta_2 - \Delta_1$, matching $\gamma_{(1)}(h_{1,1}; \Delta_1, \Delta_2) = 0 + \Delta_2 - \Delta_1 = \Delta_2 - \Delta_1$! And on the left, $\langle \Delta_4 | \Phi_3(1) | \chi_{r,s}(b) \rangle = P_{r,s}(b, \Delta_4, \Delta_3)$, which at $(1,1)$ is $\Delta_3 - \Delta_4$, matching $\gamma_{(1)}(0; \Delta_4, \Delta_3) = \Delta_3 - \Delta_4$!)*

---

## 2. Three-Point Factorization and Generic Zamolodchikov Recursion

**Lemma 2 (Singular three-point factorization).** Let $w \in M(c, h)_\ell$ be a singular vector ($L_k w = 0$ for all $k \geq 1$). Then for every partition $Z = (z_1 \geq \dots \geq z_r \geq 1)$ and every $\Delta_a, \Delta_b \in \mathbb{C}$,
\[
\langle L_{-Z} w | \Phi_b(1) | \Delta_a \rangle = \gamma_Z(h + \ell; \Delta_a, \Delta_b)\, \langle w | \Phi_b(1) | \Delta_a \rangle,
\]
where $\langle u | \Phi_b(1) | \Delta_a \rangle$ denotes the unique Virasoro three-point linear functional on $M(c, h)$ normalized by $\langle v_h | \Phi_b(1) | \Delta_a \rangle = 1$ and satisfying $\langle L_{-n} u | \Phi_b(1) | \Delta_a \rangle = \langle u | (L_0 + n \Delta_b - \Delta_a + L_n) \Phi_b(1) | \Delta_a \rangle$ for $n \geq 1$.

**Proof.** Induction on $r = \ell(Z)$. For $r = 0$, $\gamma_\emptyset = 1$ and the identity is trivial. For $r \geq 1$, write $Z = (z_1, Z')$ with $|Z'| = |Z| - z_1$ and $u = L_{-Z'} w \in M(c, h)_{\ell + |Z'|}$. By the Virasoro Ward identity for a primary $\Phi_b(1)$ of weight $\Delta_b$ between $\langle u |$ and $|\Delta_a\rangle$:
\[
\langle L_{-z_1} u | \Phi_b(1) | \Delta_a \rangle = \bigl(h + \ell + |Z'| + z_1 \Delta_b - \Delta_a\bigr) \langle u | \Phi_b(1) | \Delta_a \rangle + \langle L_{z_1} u | \Phi_b(1) | \Delta_a \rangle?
\]
WAIT — check the Ward commutation direction!
Recall from the standard primary commutator $[L_m, \Phi_b(1)] = (m \Delta_b + L_0 \text{-shift}) \Phi_b(1)$? Specifically:
\[
[L_n, \Phi_b(z)] = z^n \bigl(z \partial_z + (n + 1)\Delta_b\bigr) \Phi_b(z),
\]
so for $n \geq 1$, $L_n |\Delta_a\rangle = 0$ gives:
\[
\langle u | L_n \Phi_b(z) | \Delta_a \rangle = \langle u | [L_n, \Phi_b(z)] | \Delta_a \rangle = z^n \bigl(z \partial_z + (n + 1)\Delta_b\bigr) \langle u | \Phi_b(z) | \Delta_a \rangle.
\]
Since $\langle u | \Phi_b(z) | \Delta_a \rangle = z^{h(u) - \Delta_b - \Delta_a} \langle u | \Phi_b(1) | \Delta_a \rangle$ (where $h(u) = h + \ell + |Z'|$), we get
\[
\langle L_{-n} u | \Phi_b(1) | \Delta_a \rangle = \langle u | L_n \Phi_b(1) | \Delta_a \rangle = \bigl(h(u) + n \Delta_b - \Delta_a\bigr) \langle u | \Phi_b(1) | \Delta_a \rangle
\]
**WITHOUT ANY EXTRA $L_n u$ TERM AT ALL!!**
Wait: check that! $\langle L_{-z_1} u |$ is the contravariant dual of $L_{-z_1} u$, so $\langle L_{-z_1} u | \Phi_b(1) | \Delta_a \rangle = \langle u | L_{z_1} \Phi_b(1) | \Delta_a \rangle = \langle u | [L_{z_1}, \Phi_b(1)] | \Delta_a \rangle = (h(u) + z_1 \Delta_b - \Delta_a) \langle u | \Phi_b(1) | \Delta_a \rangle$!
In fact, this holds for **ANY** homogeneous vector $u \in M(c, h)$ of weight $h(u)$ (we do NOT even need $w$ to be singular for the 3-point factorization — singularity of $w$ is only needed to factor the Shapovalov form $B^k(L_{-Z} w, L_{-Z'} w) = \gamma_w G_{|Z|}(c, h+\ell)_{Z,Z'}$!).
Hence by induction on $r$:
\[
\langle L_{-Z} w | \Phi_b(1) | \Delta_a \rangle = \left(\prod_{j=1}^r \bigl(h + \ell + \sum_{i>j} z_i + z_j \Delta_b - \Delta_a\bigr)\right) \langle w | \Phi_b(1) | \Delta_a \rangle = \gamma_Z(h + \ell; \Delta_a, \Delta_b)\, \langle w | \Phi_b(1) | \Delta_a \rangle. \quad \square
\]

**Proposition 3 (Imported generic normalization identities).** For positive integers $r, s$ and generic $b$, let $\chi_{r,s}(b) \in M(c(b), h_{r,s}(b))_{rs}$ be the unique singular vector with $L_{-1}^{rs}$-coefficient $1$ (Iohara–Koga 2011, Props. 5.1–5.2 and Cor. 5.2). Then:
1. Its Shapovalov crossing scalar (norm derivative along $\Delta$ at fixed $c(b)$) is $\beta_{\chi_{r,s}(b)} = \mathcal{A}_{r,s}(b)^{-1}$ (Zamolodchikov 1987 / Al. Zamolodchikov 2004, eq. (14); Hadasz–Jaskólski–Suchanek 2010, §3 eq. (7); torus `paper.tex` Prop. 6.2).
2. Its sphere three-point scalar is $\langle \chi_{r,s}(b) | \Phi_b(1) | \Delta_a \rangle = P_{r,s}(b, \Delta_a, \Delta_b)$ (Zamolodchikov 1987, §2; Ribault 2019, `1809.03722` eq. (3.11) — verified symbolically for all $rs \leq 4$ in `sphere/tools/exact_sphere_block.py` with exact $+1$ sign).
Both are identities of rational functions of $b$, hence continue to every specialization where $\chi_{r,s}(b)$ is regular.

**Proposition 4 (Generic Zamolodchikov recursion for $H_N$).** Fix $N \geq 1$. For every $b \in \mathbb{C}^\times$ outside a finite set of algebraic values,
\[
H_N(c(b), \Delta, \Delta_i) = \sum_{\substack{a = (r,s) \in \mathbb{Z}_{>0}^2 \\ \ell_a = rs \leq N}} \frac{\mathcal{R}^{\mathrm{sph}}_{r,s}(b, \Delta_i)}{\Delta - h_{r,s}(b)}\, H_{N - \ell_a}\bigl(c(b), h_{r,s}(b) + rs, \Delta_i\bigr)
\]
as an identity of rational functions of $\Delta$, polynomial in $(\Delta_1, \Delta_2, \Delta_3, \Delta_4)$.

**Proof.**
Exclude $b = 0$ and the finitely many algebraic values of $b$ where any difference $h_a(b) - h_g(b)$ ($a \neq g$) or $h_a(b) + \ell_a - h_g(b)$ vanishes (Lemma 6.3 of torus `paper.tex`), or where any coefficient of $\mathcal{A}_a(b)$ or $\chi_a(b)$ has a pole, for $\ell_a, \ell_g \leq N$. Fix such $b$ and set $c = c(b)$.

For each label $a = (r, s)$ with $\ell_a = rs \leq N$, the Kac determinant $\det G_m(c, \Delta)$ has valuation $p(m - \ell_a)$ at $\Delta = h_{r,s}(b)$ for every $m \leq N$, and the singular submodule $U(\mathrm{Vir}_-)\chi_{r,s}(b)$ has dimension $p(m - \ell_a)$ at level $m$. By Smith normal form (torus `paper.tex` Lemmas 5.3–5.4), $G_m(c, \Delta)^{-1}$ has at most a simple pole at $\Delta = h_{r,s}(b)$, with residue
\[
\operatorname{Res}_{\Delta = h_{r,s}} \mathcal{B}_m(c, \Delta, \Delta_i)
= \beta_{\chi_{r,s}}^{-1} \sum_{|Z|=|Z'|=m-\ell_a} \langle L_{-Z}\chi_{r,s} | \Phi_3(1) | \Delta_4 \rangle \bigl(G_{m-\ell_a}(c, h_{r,s}+rs)^{-1}\bigr)_{Z, Z'} \langle L_{-Z'}\chi_{r,s} | \Phi_2(1) | \Delta_1 \rangle.
\]
Applying Lemma 2 and Proposition 3 yields
\[
\operatorname{Res}_{\Delta = h_{r,s}} \mathcal{B}_m(c, \Delta, \Delta_i) = \mathcal{R}^{\mathrm{sph}}_{r,s}(b, \Delta_i)\, \mathcal{B}_{m - \ell_a}(c, h_{r,s} + rs, \Delta_i)
\]
for every $\ell_a \leq m \leq N$, and $0$ for $m < \ell_a$. Multiplying by $z^{\Delta - \Delta_1 - \Delta_2}$, summing over $m$, and dividing by $\Phi(c, \Delta, \Delta_i; q)$ (using that $\Phi(c, \Delta, \Delta_i; q)$ is analytic and nonvanishing in $\Delta$ as a formal series in $q$, and $\Phi(c, h_{r,s} + rs, \Delta_i; q) / \Phi(c, h_{r,s}, \Delta_i; q) = (16 q)^{rs}$) gives
\[
\operatorname{Res}_{\Delta = h_{r,s}} H_N(c, \Delta, \Delta_i) = \mathcal{R}^{\mathrm{sph}}_{r,s}(b, \Delta_i)\, H_{N - \ell_a}(c, h_{r,s} + rs, \Delta_i),
\]
and $H_N(c, \Delta, \Delta_i)$ has no other poles in $\Delta$ (all poles of $H_N$ lie among the roots of $\det G_N(c, \Delta)$) and all its poles are simple. Finally, by **Theorem S1A** (`S1_ASYMP`), $\lim_{\Delta \to \infty} H_N(c, \Delta, \Delta_i) = 0$ for $N \geq 1$. By Liouville's theorem for rational functions of $\Delta$, $H_N$ equals the sum of its principal parts. $\square$

---

## 3. Fixed-$b_\star$ All-Order Confluence Theorem (`Theorem S1B`)

Fix any $b_\star \in \mathbb{C}^\times$, set $c_\star = c(b_\star)$ and $t = b - b_\star$, and work in the Laurent field $K_\star((t))$ where $K_\star = \mathbb{Q}(b_\star, \Delta_1, \Delta_2, \Delta_3, \Delta_4)$ with $\Delta_1, \dots, \Delta_4$ indeterminate.

For each positive Kac label $a = (r, s)$ ($\ell_a = rs$), write:
- $h_a(t) := h_{r,s}(b_\star + t) \in K_\star[[t]]$,
- $z_a(t) := h_a(t) + \ell_a \in K_\star[[t]]$,
- $R_a(t) := \mathcal{R}^{\mathrm{sph}}_{r,s}(b_\star + t, \Delta_i) \in K_\star((t))$.

For each level $N \geq 1$, let $\Lambda_N(b_\star) := \{h_a(0) : \ell_a \leq N\}$ be the set of distinct specialized Kac weights of level $\leq N$, and for $\lambda \in \Lambda_N(b_\star)$ let $\mathcal{C}^\star_{\lambda, N} := \{a = (r,s) : \ell_a \leq N,\; h_a(0) = \lambda\}$ be its collision fiber.

**Definition 5 (Shifted Laurent recursion and collision moments).**
1. Define shifted Laurent coefficients $S_{a, M}(t) \in K_\star((t))$ recursively by $S_{a, 0}(t) := 1$ and, for $M \geq 1$,
   \[
   S_{a, M}(t) := \sum_{\substack{g = (u,v) \in \mathbb{Z}_{>0}^2 \\ \ell_g = uv \leq M}} \frac{R_g(t)}{z_a(t) - h_g(t)}\, S_{g, M - \ell_g}(t).
   \]
   Every denominator $z_a(t) - h_g(t)$ is a nonzero element of $K_\star[[t]]$ (torus `paper.tex` Lemma 6.3), so the recursion is well-defined and terminates in finitely many steps.
2. Define a priori pole bounds: $\pi_g := \max\{0, -\operatorname{ord}_t R_g(t)\}$, $\sigma_{a,g} := \max\{0, \operatorname{ord}_t(z_a(t) - h_g(t))\}$, $W_{a,0} := 0$, and
   \[
   W_{a, M} := \max\bigl(\{0\} \cup \{\pi_g + \sigma_{a,g} + W_{g, M - \ell_g} : \ell_g \leq M\}\bigr).
   \]
   Then $\operatorname{ord}_t S_{a, M}(t) \geq -W_{a, M}$.
3. For $\lambda \in \Lambda_N(b_\star)$ and $a \in \mathcal{C}^\star_{\lambda, N}$, put $B_{a, N}(t) := R_a(t) S_{a, N - \ell_a}(t)$, $\delta_a(t) := h_a(t) - \lambda \in t K_\star[[t]]$, $\varepsilon_a := \operatorname{ord}_t \delta_a \geq 1$ ($\infty$ if $\delta_a \equiv 0$), $\widehat v_{a, N} := \pi_a + W_{a, N - \ell_a}$, and $\widehat M^\star_{\lambda, N} := \max_{a \in \mathcal{C}^\star_{\lambda, N}} (1 + \lfloor \widehat v_{a, N}/\varepsilon_a \rfloor)$ (with $1$ if $\varepsilon_a = \infty$). Define the **collision moments**
   \[
   \widetilde A^\star_{\lambda, k, N}(\Delta_1, \Delta_2, \Delta_3, \Delta_4) := \operatorname{CT}_t \sum_{a \in \mathcal{C}^\star_{\lambda, N}} B_{a, N}(t)\, \delta_a(t)^{k - 1} \in K_\star \qquad (1 \leq k \leq \widehat M^\star_{\lambda, N}),
   \]
   where $\operatorname{CT}_t$ extracts the $t^0$-coefficient. (For $k > \widehat M^\star_{\lambda, N}$, every summand has positive $t$-valuation, so $\widetilde A^\star_{\lambda, k, N} = 0$.)

**Lemma 6 (Backward Laurent-precision budget).** To compute $S_{a, M}(t)$ through $t^U$, it suffices to compute for each $g$ with $\ell_g \leq M$: $R_g(t)/(z_a(t) - h_g(t))$ through $t^{U + W_{g, M-\ell_g}}$ and $S_{g, M-\ell_g}(t)$ through $t^{U + \pi_g + \sigma_{a, g}}$. Propagating down the strictly level-decreasing recursion tree gives an explicit finite precision bound at every node; in particular $R_a$ through $t^{W_{a, N-\ell_a}}$, $S_{a, N-\ell_a}$ through $t^{\pi_a}$, and $\delta_a^{k-1}$ through $t^{\widehat v_{a, N}}$ suffice for all collision moments at level $N$.

**Theorem S1B (All-order confluent sphere recursion at fixed $b_\star$).** *Fix $b_\star \in \mathbb{C}^\times$ and $N \geq 1$. Then:*
1. *Every collision moment $\widetilde A^\star_{\lambda, k, N}$ lies in $\mathbb{Q}(b_\star)[\Delta_1, \Delta_2, \Delta_3, \Delta_4]$ and is computed in finitely many operations over $\mathbb{Q}(b_\star)[\Delta_1, \Delta_2, \Delta_3, \Delta_4]$ by Definition 5 and Lemma 6, with no $\varepsilon$-limit.*
2. *As a rational function of $\Delta$ with polynomial coefficients in $\Delta_1, \Delta_2, \Delta_3, \Delta_4$, the elliptic sphere coefficient admits the exact finite partial-fraction decomposition*
   \[
   H_N(c_\star, \Delta, \Delta_i) = \sum_{\lambda \in \Lambda_N(b_\star)} \sum_{k=1}^{\widehat M^\star_{\lambda, N}} \frac{\widetilde A^\star_{\lambda, k, N}(\Delta_1, \Delta_2, \Delta_3, \Delta_4)}{(\Delta - \lambda)^k}.
   \]
3. *For the cross-ratio expansion $\mathcal{B}_N(c_\star, \Delta, \Delta_i)$, substituting $H(c_\star, \Delta, \Delta_i; q) = \sum_{N=0}^\infty H_N (16 q)^N$ into $\mathcal{B}(c_\star, \Delta, \Delta_i; z) = z^{-\Delta + \Delta_1 + \Delta_2} \Phi(c_\star, \Delta, \Delta_i; q(z)) H(c_\star, \Delta, \Delta_i; q(z))$ expresses $\mathcal{B}_N$ as a finite linear combination*
   \[
   \mathcal{B}_N(c_\star, \Delta, \Delta_i) = \sum_{m=0}^N \phi_{N - m}(c_\star, \Delta, \Delta_i)\, H_m(c_\star, \Delta, \Delta_i),
   \]
   *where $\phi_r(c_\star, \Delta, \Delta_i) := [z^r]\bigl((16 q(z)/z)^{\Delta - \frac{c_\star-1}{24}} (1-z)^{\frac{c_\star-1}{24} - \Delta_2 - \Delta_3} \theta_3(q(z))^{\frac{c_\star-1}{2} - 4(\Delta_1+\Delta_2+\Delta_3+\Delta_4)} (16 q(z)/z)^m \cdots\bigr)$ — precisely, writing $(16 q(z)/z)^m \cdot \widetilde\Phi(c_\star, \Delta, \Delta_i; z) = \sum_{r=0}^\infty \psi_{m, r}(c_\star, \Delta, \Delta_i) z^r$ with $\psi_{m, r} \in \mathbb{Q}(b_\star)[\Delta, \Delta_1, \dots, \Delta_4]$ of degree $r$ in $\Delta$,*
   \[
   \mathcal{B}_N(c_\star, \Delta, \Delta_i) = \sum_{m=0}^N \psi_{m, N - m}(c_\star, \Delta, \Delta_i)\, H_m(c_\star, \Delta, \Delta_i).
   \]
   *Hence $\mathcal{B}_N(c_\star, \Delta, \Delta_i)$ has a polynomial part of degree $N$ in $\Delta$ (whose leading term is $\frac{1}{2^N N!}\Delta^N$ from $\mathcal{I}_0(z) = \frac{1}{2}z + O(z^2)$) plus a finite partial-fraction part with poles only at $\Lambda_N(b_\star)$, computed from the collision moments $\widetilde A^\star_{\lambda, k, m}$ ($1 \leq m \leq N$) by polynomial division in $\Delta - \lambda$.*

**Proof.**
By Proposition 4, at generic $b$ near $b_\star$ (i.e. as an identity in $K_\star((t))(\Delta)$ after expanding in $t = b - b_\star$), we have $S_{a, M}(t) = H_M(c(b_\star + t), z_a(t), \Delta_i)$ by induction on $M$, and
\[
H_N(c(b_\star + t), \Delta, \Delta_i) = \sum_{\lambda \in \Lambda_N(b_\star)} \sum_{a \in \mathcal{C}^\star_{\lambda, N}} \frac{B_{a, N}(t)}{\Delta - \lambda - \delta_a(t)}.
\]
Fix a formal variable $\Delta$ (or any $\Delta_0 \in \mathbb{C} \setminus \Lambda_N(b_\star)$). For $\Delta \neq \lambda$, expand
\[
\frac{1}{\Delta - \lambda - \delta_a(t)} = \sum_{k=1}^\infty \frac{\delta_a(t)^{k-1}}{(\Delta - \lambda)^k} \in K_\star(\Delta)[[t]].
\]
Multiplying by $B_{a, N}(t)$ and summing over $a \in \mathcal{C}^\star_{\lambda, N}$ gives an identity in $K_\star(\Delta)((t))$:
\[
H_N(c(b_\star + t), \Delta, \Delta_i) = \sum_{\lambda \in \Lambda_N(b_\star)} \sum_{k=1}^\infty \frac{\sum_{a \in \mathcal{C}^\star_{\lambda, N}} B_{a, N}(t) \delta_a(t)^{k-1}}{(\Delta - \lambda)^k}.
\]
On the other hand, by Definition of $H_N = P_N / \det G_N$, at fixed $\Delta \notin \Lambda_N(b_\star)$ the denominator $\det G_N(c(b_\star + t), \Delta)$ is nonzero at $t = 0$, so $H_N(c(b_\star + t), \Delta, \Delta_i)$ is **regular at $t = 0$**, i.e. lies in $K_\star(\Delta)[[t]]$, with constant term $H_N(c_\star, \Delta, \Delta_i)$!
Extracting $\operatorname{CT}_t$ on both sides (all terms with $k > \widehat M^\star_{\lambda, N}$ have positive $t$-valuation and contribute $0$ to $\operatorname{CT}_t$, while all negative powers of $t$ cancel identically in the sum over each fiber $\mathcal{C}^\star_{\lambda, N}$!) yields (2). Because the left-hand side of (2) lies in $\mathbb{Q}(b_\star)[\Delta_1, \dots, \Delta_4](\Delta)$ with poles only at $\Lambda_N(b_\star)$, the principal-part coefficients $\widetilde A^\star_{\lambda, k, N}$ lie in $\mathbb{Q}(b_\star)[\Delta_1, \dots, \Delta_4]$, proving (1). Part (3) is immediate from the defining relation between $\mathcal{B}$ and $H$ upon expanding $z^{-\Delta + \Delta_1 + \Delta_2}\Phi(c_\star, \Delta, \Delta_i; q(z)) (16 q(z))^m = z^m \sum_{r \geq 0} \psi_{m, r}(c_\star, \Delta, \Delta_i) z^r$. $\square$

*(Remark: Note why the normalization $H_N$ is essential for the confluence theorem: $\mathcal{B}_N(c, \Delta, \Delta_i)$ grows as $\frac{1}{2^N N!}\Delta^N$ as $\Delta \to \infty$ (with a non-vanishing polynomial part of degree $N$ in $\Delta$), so $\mathcal{B}_N$ does NOT satisfy a pure-pole Zamolodchikov recursion, whereas $H_N$ vanishes as $\Delta \to \infty$ by Theorem S1A and therefore admits the exact pure-pole recursion of Proposition 4 and Theorem S1B.)*
