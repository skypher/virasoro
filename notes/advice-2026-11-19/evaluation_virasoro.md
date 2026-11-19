# Evaluation of the agy advice round (2026-11-19)

Briefs: briefs/<project>.md. Answers: answers/<project>.md. Sessions: agy1–agy4, Gemini 4 Neon (High).
Checks run by the Claude session: checks/.

## virasoro (agy4, answer 13:23 Taiwan)

- Item 1 (closed form of H_M at d = h_{1,3}(b), and a mod-ℓ argument closing case (a) for every M): GOOD.
  - Lemma A1 checked exactly against the repository's direct Shapovalov computation
    (tools/direct_reconstruction.py) for M = 0..6 at (t, Δ) = (5/7, 11/13) and (−3/5, 17/19): all agree
    (checks/virasoro_lemmaA1.py, logs lemmaA1_a.log, lemmaA1_b.log).
  - The cleared polynomial P_M of step 4 agrees with M! t^{2M} ∏(2Δ − 2h_{u,1}) H_M for M = 1..6.
  - Integrality checked by reading: k! t^k c_{M,k} is a sum of multinomial coefficients times ∏(2 − i t),
    so P_M ∈ ℤ[1/2][t, Y] and P_M(0,0) = 4^M. For an odd prime ℓ | p′ (or ℓ | p, using h_{3,1}),
    t⋆ = −p′/p and Y = μ t⋆² lie in ℓℤ_ℓ, so P_M ≡ 4^M mod ℓ ≠ 0.
  - Open: a written proof of Lemma A1 for all M (agy sketches a residue-matching argument through
    the generic recursion at integer γ = 2/t > u and continuation in γ); not yet checked.
- Item 2 (order and ℓ-adic separation at d = h_{1,3}, h_{3,1} for two-vector levels): promising, rests on item 1;
  agy reports a computed tie class (p, p′) = (2^a, 3^b), b ≥ 2, where the leading 3-adic term cancels.
- Item 3 (gcd/degree obstruction and exclusive roots for case (b)): plausible complement for the ties; not checked.
- Errors flagged: dismissal of d = h_{1,3} for case (b) at (2,3), λ = 0, layer 2 (orders 2 vs 1 differ, so the
  derivative isolates one branch); a non-strict inequality at square M in cor:top-layer-sharp (conclusion unaffected).

