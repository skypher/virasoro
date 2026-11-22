import Virasoro.Sphere.Proofs.Sec3C2Spec
import Virasoro.Sphere.Proofs.Sec3C2Step3Subs

/-!
# Lemma 3.7, Step 3: the parts of the step as frozen sub-statements (sphere paper)

sphere/paper.tex l.1111–1149, in the order of the text.  The objects are those of item 12 of the
representation choices: the families `β ↦ U_β`, `β ↦ U_β^†` (`Ucf`, `Udg`), `D_k` on families
(`DkF`), the modes `α_N` (`alphaOp`), series with operator coefficients (`OpS`), the series
`f(x;W_*)/x` and its powers (`Est`), the level parts `(U(W_*)^†F_2)_n` (`Yz`).
-/

namespace Virasoro.Sphere

open MvPolynomial Finset

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1111–1114): taking the adjoint of
`D_k U(W) = -l_k^{(2)} U(W)` in the real variables `W` gives
`D_k(U(W)^†) = -U(W)^† l_{-k}^{(2)}` with `U(0)^† = id`.

Demand sheet.
- every `U` with `IsDiffeoU`;
- `U(W)^†` is the family `β ↦ U_β^†` of the adjoints of the coefficients of `W^β`, with
  `⟨U_β^† a, b⟩ = ⟨a, U_β b⟩` for the form (3.1) (l.1102–1105);
- the equation holds for every coefficient `β` and every `k ≥ 1`. -/
def Stmt_sub_c2_adj : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U →
    (∀ (β : ℕ+ →₀ ℕ) (a b : Fock), fockForm (Udg U β a) b = fockForm a (Ucf U β b)) ∧
    Udg U 0 = LinearMap.id ∧
    ∀ k : ℕ, 1 ≤ k → ∀ β : ℕ+ →₀ ℕ,
      DkF k (Udg U) β = -(Udg U β ∘ₗ ffOp (0 : ℂ) 0 (-(k : ℤ)))

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1114–1118): the free-boson current satisfies
`[l_{-k}^{(2)}, α(x)] = ∂_x(x^{1-k} α(x))`.

Demand sheet.
- `α(x) = ∑_{n≠0} α_n x^{-n-1}` is the family of its modes; at the coefficient of `x^{k-N-1}`
  the relation reads `[l_{-k}^{(2)}, α_N] = -N α_{N-k}`, for all `N ∈ ℤ` (`α_0 = 0`), `k ≥ 1`. -/
def Stmt_sub_c2_current : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (N : ℤ) (f : Fock),
    ffOp (0 : ℂ) 0 (-(k : ℤ)) (alphaOp N f) - alphaOp N (ffOp (0 : ℂ) 0 (-(k : ℤ)) f) =
      -(N : ℂ) • alphaOp (N - k) f

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1119–1127):
`U(W)^† α(x) (U(W)^†)^{-1} = f'(x;W) α(f(x;W))` before specialization.

Demand sheet.
- every `U` with `IsDiffeoU`;
- an identity of series in `W` with operator coefficients, at each power `x^{-N-1}`;
- `(U(W)^†)^{-1}` is a two-sided inverse series;
- `f'(x;W) α(f(x;W))` at `x^{-N-1}` is `ThS N`, the family `β ↦ thc β N • α_{N-|β|}`. -/
def Stmt_sub_c2_conj : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U →
    ∃ V : OpS, UdS U * V = 1 ∧ V * UdS U = 1 ∧
      ∀ N : ℤ, UdS U * MvPowerSeries.C (alphaOp N) * V = ThS N

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1128–1131): `X = f(x;W_*)` has the inverse
`x(X) = X + 1/2 + 1/(16X)`, with `√(x(X)(x(X)-1)) = X - 1/(16X)`.

Demand sheet.
- in the variable `t = x^{-1}`, with `g = f(x;W_*)/x = Est (-1)` and `1/g = Est 1`:
  `g + t/2 + t²/(16g) = 1` and `√(1-t) = g - t²/(16g)`; `qq` is the constant `1/4`. -/
def Stmt_sub_c2_fstar : Prop :=
  Est (-1) * Est 1 = 1 ∧
  Est (-1) + 2 * qq * PowerSeries.X + qq ^ 2 * PowerSeries.X ^ 2 * Est 1 = 1 ∧
  sOneC = Est (-1) - qq ^ 2 * PowerSeries.X ^ 2 * Est 1

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1131–1134): by Step 1 of Lemma 3.5,
`∮ x^{k-1} √(x(x-1)) α(x) dx · F_2 = 0` for all `k ≥ 1`.

Demand sheet.
- level by level: at level `j` the residue is the finite sum over the modes `-L ≤ N ≤ k` for
  any `L ≥ j`; `sk k N` is the coefficient of `x^N` in `x^{k-1}√(x(x-1))`;
- `F_2` by its level parts `lp F2s`. -/
def Stmt_sub_c2_input : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ (j : ℤ) (L : ℕ), j ≤ L →
    ∑ N ∈ Icc (-(L : ℤ)) k, sk k N • alphaOp N (lp F2s (j + N)) = 0

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1134–1139): applying `U(W_*)^†` and changing
variables to `X = f(x;W_*)`,
`∮ x(X)^{k-1}(X - 1/(16X)) α(X) dX · (U(W_*)^† F_2) = 0` for all `k ≥ 1`.

Demand sheet.
- every `U` with `IsDiffeoU`;
- level by level, `Yz U i = (U(W_*)^† F_2)_i`;
- the Laurent polynomial `x(X)^{k-1}(X - 1/(16X))` by its expansion
  `∑_{m=1}^k cst k m (X^m - 16^{-m} X^{-m})` (l.1140–1142); the residue of `X^M α(X)` is
  `α_M`. -/
def Stmt_sub_c2_cov : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U → ∀ k : ℕ, 1 ≤ k → ∀ n : ℤ,
    ∑ m ∈ range (k + 1), cst k m • (alphaOp m (Yz U (n + m)) -
      (1 / 16 : ℂ) ^ m • alphaOp (-(m : ℤ)) (Yz U (n - m))) = 0

/-- Lemma 3.7, Step 3 (sphere/paper.tex l.1140–1145):
`(α_m - 16^{-m} α_{-m})(U(W_*)^† F_2) = 0`, that is
`∂_{u_m}(U(W_*)^† F_2) = -(2m/16^m) u_m (U(W_*)^† F_2)` for every `m ≥ 1`.

Demand sheet.
- every `U` with `IsDiffeoU`; every `m ≥ 1`; level by level. -/
def Stmt_sub_c2_modes : Prop :=
  ∀ U : Fock →ₗ[ℂ] HH, IsDiffeoU U → ∀ m : ℕ, 1 ≤ m → ∀ n : ℤ,
    dVar m (Yz U (n + m)) =
      (-(2 * (m : ℂ) * (1 / 16 : ℂ) ^ m)) • ((uVar m : Fock) * Yz U (n - m))

theorem sub_c2_adj (hF : Cited_FeiginFuchsOperators) : Stmt_sub_c2_adj := fun _ hU =>
  ⟨fun β a b => Udg_adj hU β a b, Udg_zero hU, fun k hk β => Udg_ode hU hF k hk β⟩

theorem sub_c2_current : Stmt_sub_c2_current := fun k hk N f => ffOp_alphaOp k hk N f

theorem sub_c2_conj (hF : Cited_FeiginFuchsOperators) : Stmt_sub_c2_conj := fun U hU =>
  ⟨VdS U, UdS_mul_VdS hU, VdS_mul_UdS hU, fun N => PsS_eq_ThS hU hF N⟩

theorem sub_c2_fstar : Stmt_sub_c2_fstar := by
  refine ⟨?_, xi_one, sOneC_eq⟩
  have h := Est_mul_neg (-1)
  rwa [neg_neg] at h

theorem sub_c2_input : Stmt_sub_c2_input := fun k hk j L hL => input_residue k hk j L hL

theorem sub_c2_cov (hF : Cited_FeiginFuchsOperators) : Stmt_sub_c2_cov := fun _ hU k hk n =>
  rel hU hF k hk n

end Virasoro.Sphere
