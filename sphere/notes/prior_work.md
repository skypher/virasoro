# Prior work on sphere four-point Virasoro blocks at rational $b^2$

Verified directly against the arXiv TeX sources on 2026-11-20.

## 1. Ribault (2019), *On 2d CFTs that interpolate between minimal models* (`arXiv:1809.03722`, SciPost Phys. 6 (2019) 075), Section 3

- **§3.1 (Recursive representation, eqs. `\eqref{eq:fdz}`, `\eqref{hrec}`, `\eqref{rmn}`, `\eqref{eq:rd2}`):**
  Writes the $s$-channel sphere four-point block as $\mathcal{F}_\Delta(\{z_i\}) = \mathcal{F}^{(0)}(\{z_i\})\,\rho^\Delta H_\Delta(\rho)$ with $\rho = 16q$ and Zamolodchikov's recursion
  $$H_\Delta(\rho) = 1 + \sum_{m,n=1}^\infty \frac{\rho^{mn}}{\Delta - \Delta_{\langle m,n\rangle}} R_{m,n} H_{\Delta_{\langle m,-n\rangle}}(\rho).$$
  Expresses $R_{m,n}$ in terms of Barnes double Gamma functions and the auxiliary functions $d_\pm$.
- **§3.2 (Rational limits of generic conformal blocks, `\label{sec:rlgb}`):**
  Identifies the two sources of $\beta^2$-poles in Zamolodchikov's recursion at rational $\beta^2 = p/q$ (note Ribault's $\beta = i b$, so $\beta^2 = -b^2 = p'/p$):
  1. poles of $R_{m,n}$ due to $P_{\langle q,p\rangle} = 0$, and
  2. vanishing denominators $\Delta_{\langle m,-n\rangle} - \Delta_{\langle m',n'\rangle}$.
  Explicitly computes **two specific leading double-pole cancellations** (dropping all lower-order/simple-pole terms):
  - Eq. `\eqref{rr1}`–`\eqref{hrs}`: for $(r,s) \in [1,q-1]\times[1,p-1]$ at level $N = pq + qs - pr$ (the first layer-2 level for one sign), cancels the two divergent two-step chains to obtain the leading double-pole coefficient at $\Delta = \Delta_{\langle r,s\rangle}$, illustrated at $(p,q) = (3,2)$, $(r,s) = (1,1)$, $N = 5$ (giving $\frac{3}{11200\Delta^2}\lambda(0)\prod_\pm\lambda(\pm\frac{1}{2\beta})\lambda(\pm\beta)$).
  - Eq. `\eqref{h01}`: at level $N = q(p+1)$ for the boundary weight $(0,1)$, cancels one singular residue $R_{q,p+1}$ against one divergent two-step chain, illustrated at $(p,q) = (2,1)$, $N = 3$ (giving $\frac{1}{36\Delta^2}\lambda(0)\prod_\pm\lambda(\pm\frac{1}{\beta})$).
  - **What is NOT proved:** All-order cancellation, any triple or higher-order pole, any level past the first layer-2 level, any lower Laurent coefficient, pole-order upper bounds or sharpness, or any finite fixed-$c$ recursion. Ribault writes explicitly at the end of §3.2: *"At higher levels, we expect similar cancellations to yield poles of arbitrary orders. It would be interesting to find a recursive representation of blocks for rational central charges that would be manifestly finite, and that would explicitly exhibit these higher-order poles."*
- **§3.3 (Degenerate representations, `\label{sec:cbdr}`):**
  Verifies $R_{r,s} = 0$ for fusion-allowed generalized minimal model blocks (generic $\beta^2$). For minimal models at $\beta^2 = p/q$, states Conjecture `\ref{cj:mlb}` (`\eqref{eq:fll}`): analyticity of a minimal-model block in $(\Delta, \beta^2)$ near a fusion-allowed Kac weight. Left open.

## 2. Javerzat–Santachiara–Foda (2018), *Notes on the solutions of Zamolodchikov-type recursion relations in Virasoro minimal models* (`arXiv:1806.02790`, JHEP 08 (2018) 183), Sections 3–6

- **§3 (The 4-point conformal blocks on the sphere, `\label{section.03}`):**
  Reviews the $x$-expansion (`\eqref{cbexp}`) and Zamolodchikov's elliptic recursion (`\eqref{block_ell}`, `\eqref{H}`, `\eqref{Rmnsp}`–`\eqref{rmn}`). For generalized minimal models (§3.3), shows that regularizing $\Delta = \Delta_{m,n} + \epsilon$, $\Delta_i = \Delta_{r_i,s_i} + \epsilon_i$ with $\epsilon_i = O(\epsilon)$ removes the $(m,n)$ pole under fusion. For minimal models (§3.4–3.6), introduces $b^2 = -p'/p + \epsilon'$ ($\epsilon' = O(\epsilon)$), examines two examples in the Ising model — two singular terms at level 7 (`\eqref{Isingex}`) and five singular terms at level 20 (`\eqref{ising20}`) — and **conjectures** (§3.5) that the $\epsilon \to 0$ limit exists and gives the minimal-model block. Explicitly states (§3.6): *"If we can predict the singular terms that, at a given level, provide finite contributions, we have not been able to obtain a compact formula for these."*
- **§4 (1-point conformal blocks on the torus):** Reviews the Fateev–Litvinov / Poghossian recursion.
- **§5 (0-point functions on the torus: characters):** Introduces the fine-tuned regularization $\epsilon' = \epsilon$, $\epsilon'' = \frac{4}{\sqrt{-pp'}}\epsilon$ (`\eqref{totalreg}`), derives the finite rational limits of resonant first-step and intermediate-step factors (`\eqref{firstypeterm}`, `\eqref{secondtypeterm}`), constructs the chain-word combinatorics $U^{1,2}, D^{1,2}$ (`\eqref{transformations}`), and obtains a rational-fraction sum $C_{N(K)}$ whose equality with $(-1)^{K+1}$ is checked numerically up to $N \sim 300$ (not proved analytically).
- **§6 (Conclusions):** Confirms that cancellation in sphere four-point blocks is checked only in examples and left as a conjecture.

## 3. Ribault (2026), *Exactly solvable conformal field theories* (`arXiv:2411.17262v4`, SciPost Phys. Lect. Notes 130 (2026)), Section 4.3

- **§4.3.1 (Poles and residues):** Derives `c^{r,s}(P_1,P_2)` (`\eqref{crs}`) and `b^{r,s}` (`\eqref{brs}`) via degenerate 4-point fusion matrices, and lists explicit polynomials for $rs \leq 4$.
- **§4.3.2 (The nome):** Defines $q(z)$ via elliptic integrals and Jacobi theta functions (`\eqref{thetaids}`).
- **§4.3.3 (Zamolodchikov's recursion, `\label{sec:zrr}`):** Gives `fdq`, `hdq`, `hrec`, and explicit $h_1,\dots,h_4$. Explicitly states the **open problem**: because $R_{r,s}$ and $(\Delta_{(r,-s)}-\Delta_{(r',s')})^{-1}$ have $\Delta$-independent poles at rational $\beta^2$, Zamolodchikov's recursion is valid only for $\beta^2 \notin \mathbb{Q}$, and *"Finding a recursion for $\beta^2 \in \mathbb{Q}$ is an open problem, whose simplest incarnation is in the case of 1-point Virasoro blocks on the torus [Sto22]."*
- **§4.3.4 (Behaviour for large channel dimensions, `\label{sec:bld}`, PDF p. 69):** **Crucial rigor flag** — Ribault explicitly observes: *"The asymptotic behaviour (4.3.18), (4.3.19) of Virasoro blocks in the limit $\Delta \to \infty$ is the most important piece of the derivation of Zamolodchikov's recursion. As far as we know, there is no complete derivation of this behaviour in the literature: in particular, Zamolodchikov's original argument [Zam87] is elliptic."* He sketches how the pillow geometry $T^2/\mathbb{Z}_2$ (`\eqref{fpillow}`) and the $\hat{\mathfrak{u}}_1$ oscillator basis (cf. Besken–Datta–Kraus `1910.04169` for the heavy limit) point toward a proof.

## 4. Cho–Collier–Yin (2017/2019), *Recursive representations of arbitrary Virasoro conformal blocks* (`arXiv:1703.09805`, JHEP 04 (2019) 018), Section 2 and Appendices A–B

- **§2.1:** Inverse-Shapovalov definition of the sphere four-point $z$-expansion block $F(h,z,d_i,c)$ (`\eqref{4ptBlock}`) via 3-point descendant functions $\rho(\nu_4,\nu_3,L_{-N}\nu_h|1)$ and $\rho(L_{-M}\nu_h,\nu_2,\nu_1|1)$.
- **§2.2:** Simple pole structure and residues at generic $c$ (`\eqref{residue}`, `\eqref{eq:Ars}`, `\eqref{factorization}`, `\eqref{eq:FusionPolynomial}`, `\eqref{Residue}`), citing Zamolodchikov (1984, 2003) and Hadasz–Jaskólski–Suchanek (`hep-th/0611266`, `0907.4281`).
- **§2.3:** Rigorous algebraic derivation of the large-$c$ limit (${}_2F_1$, `\eqref{c4pt}`) and $c$-recursion (`\eqref{crecursion}`). Reviews Zamolodchikov's elliptic $h$-recursion (`\eqref{hrecursion}`), noting that the large-$h$ regular part was originally derived via semiclassical monodromy in Zamolodchikov (1987).
- **Appendices A–B:** Virasoro Ward identities (`\eqref{eq:WardIdentities}`, `\eqref{commm}`) and an explicit inductive proof of 3-point descendant factorization (`\eqref{factorization}`, `\eqref{app:fusionpolynomials}`) from the Ward identity and singularity of $\chi_{r,s}$.

## 5. Verification of 2025–2026 literature

Targeted arXiv and web searches on 2026-11-20 confirm that no 2025–2026 paper proves the finite-$c$ large-$\Delta$ limit $\lim_{\Delta\to\infty} H_N(c,\Delta,\Delta_i) = \delta_{N,0}$ (Ribault `2411.17262v4` §4.3.4 still notes none exists), all-order rational-$b^2$ cancellation, finite fixed-$c$ confluence, or Jantzen pole-order sharpness for sphere four-point Virasoro blocks. Related works cited for context: Artemev–Khromov (`arXiv:2603.08194`, Phys. Rev. D 114 (2026) 045002, WKB physics derivation of large-intermediate-dimension asymptotics for multipoint comb-channel blocks with approximations) and Ghosal–Rémy–Sun–Sun (2022 preprint, convergence and meromorphy for $c > 25$ via Liouville CFT without large-$\Delta$ asymptotics); other recent papers (Desiraju–Ghosal–Prokhorov `2407.05839` on probabilistic semiclassical torus blocks; Poghosyan–Poghosyan `2607.09177` on the $b \to 0$ light limit of torus blocks) address different regimes.

## 6. Novelty and rigor checkpoints before starting

1. **Novelty:** Both S1 (all-order exact fixed-$b_\star$ algebraic confluence for sphere four-point blocks) and S2 (all-order Jantzen pole-order upper bound, top-layer formula, and unconditional attainment at every minimal model, interior weight, and level $N$ for indeterminate external weights) are open in the literature.
2. **Critical rigor checkpoint for S1:** Unlike the torus one-point block (where $\lim_{\Delta\to\infty} F_N = p(N)$ and $\lim_{\Delta\to\infty} H_N = \delta_{N,0}$ were proved in 15 lines in `paper.tex` Lemma 4.1), for the sphere four-point block the elliptic $H$-function's large-$\Delta$ limit $\lim_{\Delta\to\infty} H_N(c,\Delta,\Delta_i) = \delta_{N,0}$ is flagged by Ribault (2026 §4.3.4) as lacking a complete proof in the literature! We must address this explicitly in `sphere/structure.md` (either by proving $\lim_{\Delta\to\infty} H_N = \delta_{N,0}$ directly, or by checking how the $z$-expansion vs $q$-expansion behaves — we must NOT silently import an unproved statement!).
