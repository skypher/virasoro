# Research advice: virasoro

## 1. Target and current hard step

- **Full target (`TOP1`, `HANDOVER.md` §1; `receipt.md`, "Current hard step"; `paper.tex`, `thm:top-layer` / `rem:top-layer-beyond`):** For every coprime pair $p,p'\ge2$, minimal-model charge $c_\star=1-6(p'-p)^2/(pp')$ ($b_\star^2=-p'/p$), interior Kac weight $\lambda=h_{r,s}(b_\star)$ ($0<r<p$, $0<s<p'$, $n_1=p'r+ps<pp'$, $n_0=p'r-ps$), and every level $N\ge1$, $H_N(c_\star,\Delta,d)$ has a pole at $\Delta=\lambda$ of order exactly $j_N(\lambda)$. By `thm:top-layer` (5.10), on each window $\ell_k\le N<\ell_{k+1}$ this is equivalent to $P_N(d):=\sum_{\pm:\,\ell^\pm_k\le N}(\tau^\pm_k(d)/\gamma^\pm_k)H_{N-\ell^\pm_k}(c_\star,\lambda+\ell^\pm_k,d)\not\equiv0$ in $\mathbb Q[d]$.
- **Narrowest unproved ranges (`paper.tex`, `cor:top-layer-sharp` (5.11) and `rem:top-layer-beyond` (5.12); `HANDOVER.md` §1):**
  - **(a) Single-vector levels** ($\ell_k\le N<\max(\ell^+_k,\ell^-_k)$, $M=N-\ell_k$, $\mu=\lambda+\ell_k$, $m^2=4pp'\mu+(p'-p)^2$): prove $H_M(c_\star,\mu,d)\not\equiv0$ for all $M\ge41$ with at least $6$ divisors and $\min(p,p')M\ge m+\max(p,p')$ (sufficiently, $\sum_{uv=M}u/D$ and $\sum_{uv=M}v/D$ with $D=(p'u-pv)^2-m^2$ do not both vanish).
  - **(b) Two-vector levels** ($\max(\ell^+_k,\ell^-_k)<N<\ell_{k+1}$, $M^\pm=N-\ell^\pm_k$): prove $P_N(d)\not\equiv0$ whenever $\max(p,p')M^\pm\ge m^\pm_k+\min(p,p')$ for at least one sign (sufficiently, $K^++(-1)^kK^-$ and $m^+_kL^+-(-1)^km^-_kL^-$ do not both vanish).

## 2. What has been tried

- **Divisor-family eliminations and uniform locus for (a)** (`HANDOVER.md` §2; `receipt.md` lines 75–97): settled $M\le40$ (`audit_kl_certificate.py`) and $\le5$ divisors; stopped at $\ge6$ divisors because resultant factors reach degrees $8$–$48$ and non-Kac common zeros split into multiple components outside $\Omega=-M(t+1/t)$.
- **Sign/dominance, interlacing, and $\ell$-adic valuations of $K,L$ for (a)** (`receipt.md` lines 29–35, 151–164): $K$ and $L$ have mixed signs; interlacing leaves $5792$ of $18702$ uncovered cases without a dominant pole; no single structural prime certifies $K\ne0$ or $L\ne0$ uniformly ($6$ of $5788$ cases lack any certifying prime $\le200$).
- **Structural nonvanishing of $H_M$ off Kac curves and single special $d=h_{1,3},h_{3,1},h_{1,5}$** (`receipt.md` lines 26–28, 60–74, 154–160): Gröbner bases proved $H_M\not\equiv0$ for all nondegenerate $(c,h)$ up to $M\le5$, out of reach at $M=6$; at $d=h_{1,3}$ the $\Delta$-numerator does not factor and $(u,1)$-composition terms never have one sign (though $H_M\ne0$ in all $3556$ tested cases).
- **One-sign combinations, second-order $d=0,1$ expansions, and fusion-root isolation for (b)** (`HANDOVER.md` §2; `receipt.md` lines 133–149): termwise one-sign combinations of $K,L$ fail in $8040$ of $10320$ outside-range cases (smallest: $(2,3)$, $\lambda=0$, $N=11$); second-order chain sums for $[d^2]H_M$ have cancelling zero denominators at $c_\star$; $d=h_{1,3}$ at $(2,3)$, $k=2$ was abandoned because both $\tau^\pm_2(1/3)=0$.
- **AGT/Nekrasov scaling for $P_N$** (`receipt.md` lines 108–114): individual Young-pair summands exceed $j_N$ resonant boxes (from $N=4$ at $(2,3)$), so higher poles cancel only after summation.

## 3. Advice

### Item 1: Exact 1-screening algebraic formula at $d=h_{1,3}(b)$ and uniform $\ell$-adic closure of all of Case (a)

**Novelty check:** Grepped `paper.tex`, `receipt.md`, `HANDOVER.md`, `runs/`, and `tools/` for `screening`, `Dotsenko`, `Beta`, `Gamma(`, `vartheta`, `theta_1`, `c_{M,k}`, `(1-z)^2`, `P_M`, `4^M`, `h_{1,3}`, and `h13`. The records only checked at $d=h_{1,3}$ whether the numerator factors in $\Delta$ (`d13.py`) and whether individual $(u,1)$-composition terms share a sign (`h13_test.py`). Neither the 1-screening algebraic representation, nor the $W=(1-z)^2/z$ expansion, nor the $\mathbb Z[\frac12][t,Y]$-integrality of $P_M$, nor the odd-prime $\ell\mid pp'$ nonvanishing appears anywhere in the repository.

**Mathematical idea:**
At $d=h_{1,3}(b)=-1-2/t$ ($t=b^2$), only labels $(u,1)$ survive in `prop:generic-recursion` (6.4). Crucially, $v=1$ is the unique row index for which the Kac weights $h_{u,1}(t)=((1-u^2)t+2(1-u))/4$ have no pole at $t=0$. Because $V_{1,3}$ carries external momentum $-b^{-1}$, the torus one-point block admits a one-screening-charge representation whose integrand depends on $z$ solely through $W=(1-z)^2/z$. This can be formulated and proved **purely algebraically** without contour integrals:

1. Put $\gamma=2/t$ and expand in $\mathbb Q(t)[W][[q]]$:
   $$\prod_{n\ge1}\left(1-\frac{q^n}{(1-q^n)^2}W\right)^{2/t}=\sum_{M\ge0}\sum_{k=0}^M c_{M,k}(t)\,W^kq^M.$$
   Since $\sum r_n=k$ in the binomial expansion and $(1-q^n)^{-2r_n}\in\mathbb Z[[q]]$, every coefficient satisfies $k!\,t^k c_{M,k}(t)\in\mathbb Z[t]$, and the unique top term is $c_{M,M}(t)=((-1)^M/(M!\,t^M))\prod_{j=0}^{M-1}(2-jt)$.
2. Introduce the linear Beta-ratio functional $\Lambda_{\nu,\gamma}$ on Laurent polynomials in $z$ by $\Lambda_{\nu,\gamma}(z^m)=B(\nu+m,\gamma+1)/B(\nu,\gamma+1)$ (a rational function of $\nu,\gamma$), with $\nu=\alpha-\gamma/2$ and $\alpha^2=((t+1)/t)^2-4\Delta/t$. Direct Beta evaluation gives
   $$\Lambda_{\nu,\gamma}\!\left(\frac{(1-z)^{2k}}{z^k}\right)=\frac{\prod_{j=1}^{2k}(\gamma+j)}{\prod_{j=1}^k(\nu-j)(\nu+\gamma+j)}=\frac{(-1)^k\prod_{j=1}^{2k}(jt+2)}{2^k t^k\prod_{j=1}^k(2\Delta-2h_{j,1}(t))}.$$
3. Define $\widetilde H_M(t,\Delta):=\sum_{k=0}^M c_{M,k}(t)\Lambda_{\nu,\gamma}(W^k)$. To prove $\widetilde H_M(t,\Delta)=H_M(c(t),\Delta,h_{1,3}(b))$, note that $\widetilde H_0=1$, $\widetilde H_M\to0$ as $\Delta\to\infty$ ($M\ge1$), and its only $\Delta$-poles are simple poles at $h_{u,1}(t)$ ($1\le u\le M$). It therefore suffices by partial-fraction uniqueness to verify $\operatorname{Res}_{\Delta=h_{u,1}(t)}\widetilde H_M(t,\Delta)=R_{u,1}(t)\widetilde H_{M-u}(t,h_{u,1}(t)+u)$ as rational functions of $\gamma=2/t$, hence for all integers $\gamma>u$. For integer $\gamma>u$, $F(z;q):=(1-z)^\gamma\prod_{n\ge1}((1-q^nz)(1-q^nz^{-1})/(1-q^n)^2)^\gamma$ is a formal series in $q$ with Laurent-polynomial coefficients in $z$ obeying the exact shift identity $F(qw;q)=(-1)^\gamma w^{-\gamma}F(w;q)$. Taking residues of $\Lambda_{\nu,\gamma}$ at $\nu=u$ gives $\operatorname{Res}_{\nu=u}\widetilde H_M=(\prod_{i=1}^u(\gamma+i)/(u-1)!)[q^Mz^{-u}]F(z;q)$; shifting $z=qw$ lowers the $q$-degree to $M-u$ and yields $(-1)^\gamma[q^{M-u}w^{\gamma-u}]F(w;q)$, which matches $(-1)^{\gamma-u}\binom{\gamma}{u}\Lambda_{u-\gamma,\gamma}(G_{M-u}(w))$ term by term in $w^m$ (with no $0/0$ singularities since $\gamma>u$). Multiplying by $d\Delta/d\nu|_{\nu=u}=-(ut+1)/2$ reproduces $R_{u,1}(t)=(-1)^{u-1}(ut+1)\prod_{x=1-u}^u(xt+2)/(2(u-1)!u!\,t^{2u})$ identically.
4. Clear denominators by multiplying $\widetilde H_M$ by $M!\,t^{2M}\prod_{u=1}^M(2\Delta-2h_{u,1}(t))$ and setting $\Delta=Y/t^2$:
   $$P_M(t,Y)=\sum_{k=1}^M \frac{M!}{k!}\Big((-1)^k k!\,t^k c_{M,k}(t)\Big)\left(\prod_{i=1}^k(it+1)\big((2i-1)t+2\big)\right)\prod_{u=k+1}^M\left(2Y+(u-1)t^2+\frac{u^2-1}{2}t^3\right).$$
   Every factor lies in $\mathbb Z[\frac12][t,Y]$, every $k<M$ summand vanishes at $(t,Y)=(0,0)$, and the $k=M$ summand gives $P_M(0,0)=2^M\cdot 2^M=4^M$.
5. For any coprime $p,p'\ge2$, at least one of $p,p'$ has an odd prime factor $\ell$. By $b\leftrightarrow b^{-1}$ symmetry (using $d=h_{3,1}$ if $p'$ is a power of $2$), assume $\ell\mid p'$. At $t=-p'/p$ and $\Delta=\mu=(m^2-(p'-p)^2)/(4pp')$, both $t\in\ell\mathbb Z_\ell$ and $Y=\mu t^2=p'(m^2-(p'-p)^2)/(4p^3)\in\ell\mathbb Z_\ell$ (since $\ell$ is odd and $\ell\nmid p$). Therefore $P_M(t,Y)\equiv 4^M\not\equiv0\pmod\ell$. Because $\det G_{M'}(c_\star,\mu)\ne0$ for all $M'\le M$ (`thm:top-layer`), $H_M(c_\star,\mu,h_{1,3}(b_\star))$ is regular and nonzero (even when individual $(u,1)$ chains collide, e.g. at $p'=2$ on the dual side).

**First exact statements to prove (with quantifiers):**
- *Lemma A1 (1-screening identity):* For all $M\ge0$, as rational functions in $\mathbb Q(t,\Delta)$,
  $$H_M\big(c(t),\Delta,h_{1,3}(b)\big)=\sum_{k=0}^M c_{M,k}(t)\,\frac{(-1)^k\prod_{j=1}^{2k}(jt+2)}{2^k t^k\prod_{j=1}^k\big(2\Delta-2h_{j,1}(t)\big)}.$$
- *Proposition A2 (Integrality and Case (a) closure):* For every $M\ge1$, $P_M(t,Y):=M!\,t^{2M}\big(\prod_{u=1}^M(2\Delta-2h_{u,1}(t))\big)H_M(c(t),\Delta,h_{1,3}(b))|_{\Delta=Y/t^2}$ lies in $\mathbb Z[\frac12][t,Y]$ (and empirically in $\mathbb Z[t,Y]$) with $P_M(0,0)=4^M$. Consequently, for all coprime $p,p'\ge2$, every interior weight $\lambda=h_{r,s}(b_\star)$, every layer $k\ge1$, and every single-vector level $\ell_k\le N<\max(\ell^+_k,\ell^-_k)$, $H_{N-\ell_k}(c_\star,\lambda+\ell_k,d)\not\equiv0$.

**Smallest concrete test case and confirmation/refutation:**
- Lemma A1 was checked directly in exact rational arithmetic against `prop:generic-recursion` for $M=1,\dots,15$ at $(t,\Delta)=(5/7,11/13)$ and $(-3/5,17/19)$ with $0$ mismatches; $P_M(t,Y)\in\mathbb Z[t,Y]$ with $P_M(0,0)=4^M$ was checked symbolically for $M=1,\dots,5$ and at integer points ($t=3,5,7,11$) up to $M=40$ with $0$ exceptions.
- To confirm in the paper's audit suite, replay Lemma A1 symbolically for $M\le5$ and check $P_M(-p'/p,\mu t^2)\equiv 4^M\pmod\ell$ at the first open Case (a) level $M=42$ (which has $8$ divisors); any rational denominator divisible by an odd prime or any mismatch in the residue verification at integer $\gamma>u$ would refute the proof.

**Why it succeeds where recorded attempts failed:**
Recorded attempts worked either at $d=0,1$ (mixed-sign divisor sums $K,L$ whose prime divisors vary erratically with $m,M$) or on individual $(u,1)$ chains at $d=h_{1,3}$ (mixed signs and collisions when $p'=2$). The 1-screening expansion regroups all chains into a polynomial in $(t,\Delta t^2)$ whose constant term $4^M$ is independent of $(p,p',r,s,k,m)$ and is a unit modulo every odd prime $\ell\mid pp'$. This closes Case (a) completely and also supersedes the $M\le40$ computer certificate and the $\le5$-divisor Diophantine arguments in `cor:top-layer-sharp`.

---

### Item 2: Order and $\ell$-adic valuation separation of two-term levels at $d=h_{1,3}(b_\star)$ and $d=h_{3,1}(b_\star)$

**Novelty check:** Grepped `paper.tex`, `receipt.md`, `HANDOVER.md`, and `runs/toplayer/` for `ord_`, `mult`, `tau_roots`, `h_{1,3}`, `h_{3,1}`, `padic`, and `gamma^+`. The repo checked $p$-adic valuations only for $K,L$ in Case (a) (`padic.py`, `padic_L.py`), and rejected $d=h_{1,3}$ for Case (b) after observing $\tau^\pm_2(1/3)=0$ at $(2,3)$ (`receipt.md` lines 145–147) without checking root multiplicities or extracting the closed form of $\gamma^+_k/\gamma^-_k$ from `prop:layer-coefficients`.

**Mathematical idea:**
By `lem:singular-factorization` (5.5) and `lem:regular-everywhere` (6.6), the torus norms $\tau^\pm_k(d)$ are explicit monic products of linear factors $(d-d_x)$ with $d_x=(x^2-(p'-p)^2)/(4pp')$:
$$\tau^+_{2j+1}=\mathcal P_{r+jp,\,s+jp'},\quad \tau^-_{2j+1}=\mathcal P_{(j+1)p-r,\,(j+1)p'-s},$$
$$\tau^+_{2j}=\mathcal P_{r+(j-1)p,\,s+(j-1)p'}\mathcal P_{(2j-1)p+r,\,p'-s},\quad \tau^-_{2j}=\mathcal P_{r+(j-1)p,\,s+(j-1)p'}\mathcal P_{p-r,\,(2j-1)p'+s}.$$
By `prop:layer-coefficients` (6.7), $\gamma^\pm_k=[d^k]\tau^\pm_k(d)/(c_k(\pm\rho)^k)$ is known in closed form, so for any root $d_0=d_{x_0}$ of multiplicity $e_\pm=\operatorname{ord}_{d=d_0}\tau^\pm_k(d)$, the leading coefficient $[(d-d_0)^{e_\pm}](\tau^\pm_k/\gamma^\pm_k)$ is an explicit product of $(x_0^2-x^2)$ divided by $((p'-p)^2-x^2)$. Combine this with Item 1, which gives the **exact** $\ell$-adic valuation of $H_M(c_\star,\mu^\pm_k,h_{1,3}(b_\star))$ for every odd prime $\ell\mid p'$:
$$v_\ell\big(H_M(c_\star,\mu^\pm_k,h_{1,3})\big)=-v_\ell(M!)-2Mv_\ell(p')-\sum_{u=1}^M v_\ell\big(2\mu^\pm_k-2h_{u,1}(t)\big)$$
(and dually at $d=h_{3,1}(b_\star)$ for every odd prime $\ell\mid p$). On any two-term level $\max(\ell^+_k,\ell^-_k)<N<\ell_{k+1}$:

1. **Order separation:** Whenever $e_+=\operatorname{ord}_{d=h_{1,3}}\tau^+_k\ne e_-=\operatorname{ord}_{d=h_{1,3}}\tau^-_k$ (for $p'$ having an odd prime factor, or dually at $h_{3,1}$ for $p$), extracting $[(d-h_{1,3})^{\min(e_+,e_-)}]P_N(d)$ kills the higher-order branch and leaves a nonzero multiple of $H_{M^{\min}}(c_\star,\mu^{\min}_k,h_{1,3})\ne0$. For example, when $k=1$ and $s\in\{1,p'-1\}$ with $p'\ge3$ odd, one of $e_\pm$ is $0$ and the other is $\ge1$, closing that entire infinite family immediately.
2. **Exact $\ell$-adic valuation separation:** When $e_+=e_-=e$, the two branches have valuations $V_\ell^\pm(N)=v_\ell([(d-h_{1,3})^e](\tau^\pm_k/\gamma^\pm_k))+v_\ell(H_{M^\pm}(c_\star,\mu^\pm_k,h_{1,3}))$. Because $M^+\ne M^-$ and $v_\ell(H_M)$ drops by at least $v_\ell(p')$ per unit increase in $M$, $V_\ell^+(N)\ne V_\ell^-(N)$ forces $[(d-h_{1,3})^e]P_N(d)\ne0$.

**First exact statement to prove (with quantifiers):**
- *Proposition B1 (Two-term $\ell$-adic criterion):* For all coprime $p,p'\ge2$, interior $\lambda=h_{r,s}(b_\star)$, $k\ge1$, $\max(\ell^+_k,\ell^-_k)<N<\ell_{k+1}$, and any odd prime $\ell\mid p'$: let $x_0=|p'-3p|$, let $m^\pm(x)$ be the multiplicity of $d_x$ in $\tau^\pm_k$, and let $e_\pm=m^\pm(x_0)$. If $e_+\ne e_-$, then $P_N(d)\not\equiv0$. If $e_+=e_-$, set
  $$V_\ell^\pm(N):=\sum_{x\ne x_0}m^\pm(x)\,v_\ell(x_0^2-x^2)-\sum_{x\ne|p'-p|}m^\pm(x)\,v_\ell\big((p'-p)^2-x^2\big)-v_\ell(M^\pm!)-2M^\pm v_\ell(p')-\sum_{u=1}^{M^\pm}v_\ell\big(2\mu^\pm_k-2h_{u,1}(t)\big).$$
  If $V_\ell^+(N)\ne V_\ell^-(N)$, then $[(d-h_{1,3})^{e_+}]P_N(d)\ne0$ and hence $P_N(d)\not\equiv0$. The dual criterion holds with $p\leftrightarrow p'$ and $h_{1,3}\leftrightarrow h_{3,1}$ for every odd prime $\ell\mid p$.
- *Next analytic target (speculative):* Prove unconditionally that when $p'$ is prime (or when $\ell\ge5$ is a prime dividing $p'$ with $v_\ell(p')=1$, or $\ell=3$ with $v_3(p')=1$), $e_+=e_-$ implies $V_\ell^+(N)\ne V_\ell^-(N)$.

**Smallest concrete test case and confirmation/refutation:**
- Smallest case where the paper's one-sign $K,L$ method fails: $(p,p')=(2,3)$, $\lambda=0$, $k=2$, $N=11$ ($M^+=4$, $M^-=6$). At $d=h_{1,3}=1/3$, $e_+=2\ne e_-=1$, so Order separation immediately proves $P'_{11}(1/3)\ne0$.
- Smallest equal-order case: $(p,p')=(2,5)$, $(r,s)=(1,2)$, $k=1$, $N=4$ ($M^+=2$, $M^-=1$). Here $e_+=e_-=1$ and $V_5^+(4)=-2\ne V_5^-(4)=-1$.
- Broad test already executed: **0 undecided cases** across all two-term levels for $pp'\le60$, $k\le4$ (combining $h_{1,3}$ and $h_{3,1}$), and **0 undecided cases** across $40128$ two-term levels with $p\in\{2,4\}$, $p'<25$ odd, $k\le4$. Across $pp'\le80$, $k\le4$, there are **0** single-prime ties for $\ell\ge5$ or for $\ell=3$ with $v_3(p')=1$.
- **Exact boundary / refutation of single-point universality:** At $(p,p')=(8,9)$, $(r,s)=(3,5)$, $k=1$, $N\in\{23,29,32,38,41\}$, $p=8$ has no odd prime factor and $p'=3^2$ has $3\mid x_0=|9-24|=15$, producing $V_3^+(N)=V_3^-(N)$ (and at $N=23,32,41$ the leading mod-$3$ residues also cancel). Thus $(p,p')=(2^a,3^b)$ with $b\ge2$ cannot be closed solely by the leading $3$-adic term of $[(d-h_{1,3})^e]P_N(d)$ and needs either higher $3$-adic / $d$-derivative terms or Item 3.

**Why it succeeds where recorded attempts failed:**
First-order derivatives at $d=0,1$ always see the same order $k$ in both branches and mix both branches at comparable archimedean sizes. At $d=h_{1,3}$ / $h_{3,1}$, the branches either have different vanishing orders (collapsing Case (b) to Case (a)) or strongly separated $\ell$-adic poles governed by the closed-form valuation of Item 1.

---

### Item 3: Coprime-factor divisibility $d(d-1)\widetilde\tau^\pm_k\mid H_{M^\mp}$ and exclusive-root isolation for Case (b)

**Novelty check:** Grepped `paper.tex`, `receipt.md`, `HANDOVER.md`, and `runs/toplayer/` for `tau_tilde`, `gcd.*tau`, `exclusive root`, and `d_max`. None appear in the repository; the records never factored out $g_k=\gcd(\tau^+_k,\tau^-_k)$ or used the degree/exclusive-root constraints on $H_{M^\mp}$.

**Mathematical idea:**
Write $g_k(d):=\gcd(\tau^+_k(d),\tau^-_k(d))$ and $\tau^\pm_k=g_k\widetilde\tau^\pm_k$ in $\mathbb Q[d]$. Because $\operatorname{ord}_{d=0}\tau^\pm_k=\operatorname{ord}_{d=1}\tau^\pm_k=k$ (`prop:layer-coefficients`) while $d(d-1)\mid H_{M^\pm}$ (`lem:d-derivatives`), the polynomials $\widetilde\tau^+_k,\widetilde\tau^-_k,d(d-1)$ are pairwise coprime. Hence $P_N(d)\equiv0$ implies
$$d(d-1)\,\widetilde\tau^+_k(d)\mid H_{M^-}(c_\star,\mu^-_k,d) \qquad\text{and}\qquad d(d-1)\,\widetilde\tau^-_k(d)\mid H_{M^+}(c_\star,\mu^+_k,d).$$
Since $\deg_d H_M\le2M$, this gives two immediate tools complementary to Item 2:
1. **Degree obstruction:** If $2+\deg\widetilde\tau^+_k>2M^-$ or $2+\deg\widetilde\tau^-_k>2M^+$, then $P_N\not\equiv0$ immediately. This already excludes $740$ of $11200$ two-term cases for $pp'\le30,k\le4$, and in particular kills the smallest $(8,9,3,5,1)$ tie of Item 2 ($N=23$, where $\deg\widetilde\tau^-_1=16$, so $2+16=18>16=2M^+$).
2. **Guaranteed exclusive roots (for $(2^a,3^b)$ ties):** For every $(p,p',r,s,k)$, the larger-level branch has a strictly larger maximum root $d_{\max}$ than the other branch: for $k=2j+1$, $X^-_{2j+1}-X^+_{2j+1}=4(pp'-n_1)>0$; for $k=2j$, $|X^+_{2j}-X^-_{2j}|=4|n_0|>0$, where $X^\pm_k=\max\{|p'k_1\pm pl_1|\}$ in $\tau^\pm_k$. Evaluating $P_N$ at any root $d_0$ of $\widetilde\tau^+_k$ (resp. $\widetilde\tau^-_k$) isolates $H_{M^-}(c_\star,\mu^-_k,d_0)$ (resp. $H_{M^+}(c_\star,\mu^+_k,d_0)$). *Speculation:* for the $(2^a,3^b)$ ($b\ge2$) valuation-tie class of Item 2, test whether $\widetilde\tau^\pm_k$ always contains a degenerate exclusive root $h_{1,2m+1}(b_\star)$ (e.g. $h_{1,9}$ at $(8,9,3,5,1)$, where $h_{1,9}=-4-20/t$ has $3\nmid20$) or whether an exact $3$-adic bound on $H_{M^\mp}(c_\star,\mu^\mp_k,d_{\max})$ via the $t$-expansion at $d_{\max}=O(1/t)$ closes the remaining $(2^a,3^b)$ ties (note that for general $d=X/t$, $h_{u,v}(t)$ has a $t^{-1}$ pole for $v\ge2$, so a $3$-adic proof at $d\ne h_{1,3}$ must control the $v\ge2$ denominators).

**First exact statement to prove (with quantifiers):**
- *Lemma C1:* For all coprime $p,p'\ge2$, interior $\lambda=h_{r,s}(b_\star)$, $k\ge1$, and $\max(\ell^+_k,\ell^-_k)<N<\ell_{k+1}$, let $\tau^\pm_k=g_k\widetilde\tau^\pm_k$ with $g_k=\gcd(\tau^+_k,\tau^-_k)$. Then:
  (i) $\max(\deg\widetilde\tau^+_k,\deg\widetilde\tau^-_k)\ge2|\ell^+_k-\ell^-_k|>0$, and the larger-level branch has a simple root $d_{\max}$ that is not a root of the smaller-level branch;
  (ii) if $2+\deg\widetilde\tau^+_k>2(N-\ell^-_k)$ or $2+\deg\widetilde\tau^-_k>2(N-\ell^+_k)$, then $P_N(d)\not\equiv0$.

**Smallest concrete test case and confirmation/refutation:**
- First $(2^a,3^b)$ tie outside the degree bound: $(p,p')=(8,9)$, $(r,s)=(3,5)$, $k=1$, $N=32$ ($M^+=17$, $M^-=12$, $\deg\widetilde\tau^+_1=6$, $\deg\widetilde\tau^-_1=16$). Evaluate $H_{12}(c_\star,\mu^-_1,d)$ at the exclusive root $d=h_{1,9}(b_\star)$ (and at $d_{\max}=d_{117}$) and inspect its $3$-adic valuation; a uniform nonvanishing mechanism on the $N=32,41$ ties of $(8,9,3,5,1)$ would confirm this route as the complement to Item 2, while vanishing of $H_{M^-}$ at a single exclusive root would show that multiple roots of $\widetilde\tau^+_k$ must be used together.

**Why it succeeds where recorded attempts failed:**
It exploits the full polynomial factorization of $\tau^\pm_k(d)$ across all roots (not just $d=0,1$), using exact divisibility rather than termwise positivity, and specifically targets the $(2^a,3^b)$ regime where $3\mid|p'-3p|$ causes Item 2's leading valuation at $d=h_{1,3}$ to tie.

## 4. Errors or overlooked points

1. **Mistaken dismissal of $d=h_{1,3}$ for branch isolation in Case (b) (`receipt.md` lines 145–147; `HANDOVER.md` §2, row 5):** Both files state that at $(2,3)$, $\lambda=0$, layer $2$, $d_0=h_{1,3}=1/3$ "gives nothing" because it is a root of both $\tau^+_2=\tau^-_1\mathcal P_{1,5}$ and $\tau^-_2=\tau^-_1\mathcal P_{3,1}$. In fact, $\operatorname{ord}_{d=1/3}\tau^+_2=2$ (one root from $\tau^-_1=\mathcal P_{1,2}$ and one from $\mathcal P_{1,5}$) whereas $\operatorname{ord}_{d=1/3}\tau^-_2=1$, so $\partial_dP_N(1/3)=((\tau^-_2)'(1/3)/\gamma^-_2)H_{M^-}(0,\mu^-_2,1/3)$ **does** isolate the minus branch (and settles $(2,3),\lambda=0,N=11$ immediately via Item 1). Moreover, $\tau^+_2$ also has exclusive simple roots at $d=(15^2-1)/24=28/3$ and $d=(21^2-1)/24=55/3$.
2. **Incorrect claim that higher Taylor coefficients of $\tau^\pm_k/\gamma^\pm_k$ need the next order of the scaling limit (`receipt.md` lines 139–141):** Line 140 says the next Taylor coefficient of $\tau/\gamma$ is "not given by Prop 6.7; would need the next order of the scaling limit." Since $\gamma^\pm_k$ is independent of $d$ and $\tau^\pm_k(d)$ is explicitly factored by `lem:singular-factorization` and `lem:regular-everywhere`, `prop:layer-coefficients` already determines $\gamma^\pm_k=[d^k]\tau^\pm_k/(c_k(\pm\rho)^k)$ in closed form (as `receipt.md` itself notes on line 105), and hence determines **all** Taylor coefficients of $\tau^\pm_k(d)/\gamma^\pm_k$ at every $d_0\in\mathbb C$.
3. **Minor inequality slip for square $M^\pm$ in `cor:top-layer-sharp` (`paper.tex` line 1077):** The proof states "pairing $(u,v)$ with $(v,u)$, $u\ge v$, gives $|f(v,u)|<f(u,v)$ if $p'>p$." When $M^\pm$ is a perfect square and $u=v$, $f(v,u)=f(u,v)=(p'-p)u>0$, so $|f(v,u)|=f(u,v)$ rather than strict inequality. The conclusion $K^\pm<0$ still holds, because the unpaired $u=v$ term has the required sign; the wording should split $u>v$ (paired) and $u=v$ (single positive/negative term).
4. **Overlooked common-modulus identity for $L^\pm$ in Case (b) (`paper.tex` `rem:top-layer-beyond` lines 1096–1099; `receipt.md` lines 133–138):** Using $(p'u+pv)^2-(p'u-pv)^2=4pp'uv$ and $(m^\pm_k)^2+4pp'M^\pm=n_0^2+4pp'N=:C_N$, the denominators of $L^+$ and $L^-$ share the **same** constant $C_N$: $L^\pm=\frac{2pp'}{p+p'}\sum_{uv=M^\pm}g/(C_N-g^2)$ with $g=p'u+pv$. If anyone revisits the $d=1$ arithmetic condition $m^+_kL^+-(-1)^km^-_kL^-=0$, both sums are evaluations of the single family $\sum_{uv=M}g/(x-g^2)$ at the same point $x=C_N$.

END OF ADVICE
