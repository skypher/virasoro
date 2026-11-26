import Virasoro.Statements.Sec7ChainValues
import Virasoro.Statements.Sec5c
import Virasoro.Orbit

/-!
# Frozen statements: Section 8.1 of `paper.tex` (coefficients on the diagonal)

Paper: `paper.tex`, Section 8.1 (`sec:diagonal`), Lemma 8.3 to Corollary 8.9, version of
2026-11-27.

Reading conventions (besides those of `Virasoro.Statements.Sec7FixedCharge`).
* The setting of Section 8 is `MinimalSetting p p' r s b`.  A node is a pair `(ε, k)`:
  `μ^ε_k = λ + ℓ^ε_k` for `k ≥ 1`, and `λ` for `k = 0` (either sign).  Its layer is `k`, its
  weight `muOrb`, its level above `λ` is `ellOrb`, its signed momentum `S` is `nOrb` for
  `ε = true` and `-nOrb` for `ε = false` (so `S_λ = n₀`), and its position is `±k/2`.
* The chain functions from a node `a` to a node `μ` of larger layer are
  `chainFnC b (weight a) (ℓ_μ - ℓ_a) k j` (Definition 7.9 with `a` in place of `λ`).
* A chain from `a` to `μ` in the sense of Lemma 8.3(iii) is the list of its nodes
  `[x₀, …, x_{n+1}]` (`nodeChains`); its labels are `nodeLabel x_i x_{i+1}`, and
  `P^{(k)}_γ δ_{g_n}^j/j!` is `chainProd`.  The identification of the recursively defined
  `chainFnC` with the sum over these lists is the last assertion of Lemma 8.3(iii).
* "`R_g = ρ_g t^{1-Δ} + O(t^{2-Δ})`" is `1 - Δ ≤ orderTop R_g` with `ρ_g` the coefficient of
  `t^{1-Δ}`; "nonzero in `K⋆`" is nonzero in `ℂ(d)`.
* "A rational number that depends only on the positions of the nodes (not on `p, p', r, s` or
  `d`)" is a function of the nodes, the same for every minimal-model setting.
-/

namespace Virasoro

open scoped LaurentSeries Polynomial

/-- A node of the braided diagram: `(ε, k)` is `μ^ε_k` for `k ≥ 1` and `λ` for `k = 0`. -/
abbrev Node := Bool × ℕ

section Nodes

variable (p p' r s : ℕ)

/-- The signed momentum `S_ν`. -/
def nodeS (a : Node) : ℤ := if a.1 then nOrb p p' r s a.1 a.2 else -nOrb p p' r s a.1 a.2

/-- The position `π_ν = ±k/2`. -/
def nodePos (a : Node) : ℚ := if a.1 then (a.2 : ℚ) / 2 else -((a.2 : ℚ) / 2)

/-- The weight of the node. -/
noncomputable def nodeWt (a : Node) : ℂ := muOrb p p' r s a.1 a.2

/-- The level `ℓ^ε_k` of the node above `λ` (`0` for `λ`). -/
def nodeLev (a : Node) : ℕ := ellOrb p p' r s a.1 a.2

/-- The label of weight `ν` leading to `ν'` of Lemma 8.3(ii):
`(ε (S_{ν'} + S_ν)/(2p'), ε (S_{ν'} - S_ν)/(2p))` with `ε = sgn S_{ν'}`. -/
def nodeLabel (ν ν' : Node) : Label :=
  let S := nodeS p p' r s ν
  let S' := nodeS p p' r s ν'
  let e : ℤ := if 0 < S' then 1 else -1
  ((e * (S' + S) / (2 * p')).toNat, (e * (S' - S) / (2 * p)).toNat)

/-- The possible first steps `FS(a → μ)`: the nodes `θ` with `L_θ - L_a` odd and `L_θ < L_μ`,
and `μ` itself when `L_μ - L_a` is odd. -/
def firstSteps (a μ : Node) : Finset Node :=
  ((Finset.univ : Finset Bool) ×ˢ ((Finset.Ioo a.2 μ.2).filter fun k => (k - a.2) % 2 = 1)) ∪
    (if (μ.2 - a.2) % 2 = 1 then {μ} else ∅)

/-- The chains from `a` to `μ` of Lemma 8.3(iii), as lists of nodes `[a, x₁, …, μ]`. -/
def nodeChains (a μ : Node) : Finset (List Node) :=
  if a.2 < μ.2 then
    (if (μ.2 - a.2) % 2 = 1 then {[a, μ]} else ∅) ∪
      ((firstSteps a μ).filter (· ≠ μ)).attach.biUnion fun θ =>
        (nodeChains θ.1 μ).image (a :: ·)
  else ∅
termination_by μ.2 - a.2
decreasing_by
  have h := (Finset.mem_filter.1 θ.2).1
  simp only [firstSteps, Finset.mem_union, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_filter, Finset.mem_Ioo] at h
  rcases h with h | h
  · omega
  · split_ifs at h <;> simp_all

end Nodes

section Chains

variable (p p' r s : ℕ) (b : ℂ)

/-- `c^{(k)}_{a→μ,j}` for nodes `a`, `μ`. -/
noncomputable def nodeChain (a μ : Node) (k j : ℕ) : Kd⸨X⸩ :=
  chainFnC b (nodeWt p p' r s a) (nodeLev p p' r s μ - nodeLev p p' r s a) k j

/-- `Top(a → μ) = c^{(D)}_{a→μ,0}(b⋆)`, `D = L_μ - L_a`. -/
noncomputable def nodeTop (a μ : Node) : Kd := (nodeChain p p' r s b a μ (μ.2 - a.2) 0).coeff 0

/-- The residue germ `R_g` of the label from `ν` to `ν'`. -/
noncomputable def nodeR (ν ν' : Node) : Kd⸨X⸩ := RG (bsC b) dvar (nodeLabel p p' r s ν ν')

/-- The germ `δ_g` of the label from `ν` to `ν'`. -/
noncomputable def nodeDel (ν ν' : Node) : Kd⸨X⸩ := delG (bsC b) (nodeLabel p p' r s ν ν')

/-- The product `∏_{i≥1} R_{g_i}/(δ_{g_{i-1}} - δ_{g_i}) · δ_{g_n}^j/j!` of a chain, entered from the
label with germ `y`; `ν` is the current node and `l` the remaining nodes. -/
noncomputable def chainTailProd (j : ℕ) : Kd⸨X⸩ → Node → List Node → Kd⸨X⸩
  | y, _, [] => y ^ j / (j.factorial : Kd⸨X⸩)
  | y, ν, ν' :: l =>
      nodeR p p' r s b ν ν' / (y - nodeDel p p' r s b ν ν') *
        chainTailProd j (nodeDel p p' r s b ν ν') ν' l

/-- `P^{(k)}_γ δ_{g_n}^j/j!` for a chain `γ = [x₀, x₁, …, x_{n+1}]`. -/
noncomputable def chainProd (k j : ℕ) : List Node → Kd⸨X⸩
  | x₀ :: x₁ :: l =>
      nodeR p p' r s b x₀ x₁ * nodeDel p p' r s b x₀ x₁ ^ (k - 1) *
        chainTailProd p p' r s b j (nodeDel p p' r s b x₀ x₁) x₁ l
  | _ => 0

/-- `ρ_g`, the coefficient of `t^{1-Δ}` in `R_g` for the label from `ν` to `ν'`. -/
noncomputable def nodeRho (ν ν' : Node) : Kd :=
  (nodeR p p' r s b ν ν').coeff (1 - ((ν'.2 : ℤ) - ν.2))

/-- `ς = b⋆/(2p'²)` and `K = p'² - p²`. -/
noncomputable def varsig : ℂ := b / (2 * (p' : ℂ) ^ 2)

/-- `h_{νν'} = ς (K - S_ν S_{ν'})`, the slope `h'_g(b⋆)` of the label from `ν` to `ν'`. -/
noncomputable def nodeH (ν ν' : Node) : Kd :=
  pt (varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) -
    (nodeS p p' r s ν : ℂ) * (nodeS p p' r s ν' : ℂ)))

/-- The links `∏_{i=1}^n (h_{i-1} - h_i)` of a chain. -/
noncomputable def chainLinks : List Node → Kd
  | x₀ :: x₁ :: x₂ :: l =>
      (nodeH p p' r s b x₀ x₁ - nodeH p p' r s b x₁ x₂) * chainLinks (x₁ :: x₂ :: l)
  | _ => 1

/-- The residue product `∏_{i=0}^n ρ_{g_i}` of a chain. -/
noncomputable def chainRho : List Node → Kd
  | x₀ :: x₁ :: l => nodeRho p p' r s b x₀ x₁ * chainRho (x₁ :: l)
  | _ => 1

/-- `w_γ = ∏ ρ_{g_i} / ∏ (h_{i-1} - h_i)`. -/
noncomputable def chainW (γ : List Node) : Kd := chainRho p p' r s b γ / chainLinks p p' r s b γ

/-- `h_0` (first label) and `h_n` (last label) of a chain. -/
noncomputable def chainH0 : List Node → Kd
  | x₀ :: x₁ :: _ => nodeH p p' r s b x₀ x₁
  | _ => 0

noncomputable def chainHn : List Node → Kd
  | [x₀, x₁] => nodeH p p' r s b x₀ x₁
  | _ :: l => chainHn l
  | [] => 0

end Chains

/-- The closed form of Theorem 8.8: with `n = ⌊(D-1)/2⌋`,
`f_{2i}(l,D) = (-1)^i C(n,i) C(l+n,i)/C(l+D-1,i)`, `f_{2i+1} = f_{2i}` for `D` even, `0` for `D` odd. -/
def fDiag (l D j : ℕ) : ℚ :=
  if j % 2 = 1 ∧ D % 2 = 1 then 0
  else (-1 : ℚ) ^ (j / 2) * (((D - 1) / 2).choose (j / 2) : ℚ) *
      ((l + (D - 1) / 2).choose (j / 2) : ℚ) / ((l + D - 1).choose (j / 2) : ℚ)

/-- Lemma 8.3 (`lem:node-labels`).  (i) For every positive label `g`,
`h'_g(b⋆) = b⋆/(2p'²) (p'² - p² - x_g y_g)` with `x_g = p'u - pv`, `y_g = p'u + pv`.
(ii) For nodes `ν, ν'` with `Δ = L_{ν'} - L_ν` odd and positive there is exactly one positive
label of weight `ν` leading to `ν'`, namely `nodeLabel ν ν'`, and `x_g y_g = S_ν S_{ν'}`.
(iii) Every positive label whose weight is a node leads to a node of larger layer and of the
other class; so the chains from `a` to `μ` are the node sequences with odd positive steps:
`c^{(k)}_{a→μ,j} = ∑_{γ ∈ nodeChains a μ} P^{(k)}_γ δ_{g_n}^j/j!`. -/
def Stmt_lem_node_labels : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    (∀ g : Label, 0 < g.1 → 0 < g.2 →
      (delG (bsC b) g).coeff 1 =
        pt (varsig p' b * (((p' : ℂ) ^ 2 - (p : ℂ) ^ 2) -
          (((p' : ℤ) * g.1 - p * g.2 : ℤ) : ℂ) * (((p' : ℤ) * g.1 + p * g.2 : ℤ) : ℂ)))) ∧
    (∀ ν ν' : Node, ν.2 < ν'.2 → (ν'.2 - ν.2) % 2 = 1 →
      (∀ g : Label, 0 < g.1 → 0 < g.2 →
        (kacHL g b = nodeWt p p' r s ν ∧ kacHL g b + (g.lvl : ℂ) = nodeWt p p' r s ν' ↔
          g = nodeLabel p p' r s ν ν')) ∧
      0 < (nodeLabel p p' r s ν ν').1 ∧ 0 < (nodeLabel p p' r s ν ν').2 ∧
      ((p' : ℤ) * (nodeLabel p p' r s ν ν').1 - p * (nodeLabel p p' r s ν ν').2) *
          ((p' : ℤ) * (nodeLabel p p' r s ν ν').1 + p * (nodeLabel p p' r s ν ν').2) =
        nodeS p p' r s ν * nodeS p p' r s ν') ∧
    (∀ (ν : Node) (g : Label), 0 < g.1 → 0 < g.2 → kacHL g b = nodeWt p p' r s ν →
      ∃ ν' : Node, ν.2 < ν'.2 ∧ (ν'.2 - ν.2) % 2 = 1 ∧
        kacHL g b + (g.lvl : ℂ) = nodeWt p p' r s ν') ∧
    (∀ (a μ : Node) (k j : ℕ), a.2 < μ.2 → 1 ≤ k →
      nodeChain p p' r s b a μ k j = ∑ γ ∈ nodeChains a μ, chainProd p p' r s b k j γ)

/-- Lemma 8.4 (`lem:node-poles`).  For the label `g` of Lemma 8.3(ii),
`R_g = ρ_g t^{1-Δ} + O(t^{2-Δ})` with `ρ_g ≠ 0` in `K⋆`. -/
def Stmt_lem_node_poles : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ ν ν' : Node, ν.2 < ν'.2 → (ν'.2 - ν.2) % 2 = 1 →
      (((1 - ((ν'.2 : ℤ) - ν.2) : ℤ) : WithTop ℤ) ≤ (nodeR p p' r s b ν ν').orderTop) ∧
        nodeRho p p' r s b ν ν' ≠ 0

/-- Lemma 8.5 (`lem:node-leading`).  (i) For a chain `γ` from `a` to `μ`, `D = L_μ - L_a`:
`P^{(k)}_γ δ_{g_n}^j/j! = w_γ h_0^{k-1} h_n^j t^{k+j-D}/j! + O(t^{k+j-D+1})`; hence
`∑_γ w_γ h_0^{k-1} h_n^j = 0` for `k + j < D`, and `c^{(k)}_{a→μ,j}(b⋆) = (1/j!) ∑_γ w_γ h_0^{k-1} h_n^j`
for `k + j = D`.  (ii) `FS(a → μ)` has `D` elements, the `h_{aθ}` are distinct, and
`F(θ) = ∑_{γ : x₁ = θ} w_γ = Top(a→μ) / ∏_{θ' ≠ θ} (h_{aθ} - h_{aθ'})`. -/
def Stmt_lem_node_leading : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ a μ : Node, a.2 < μ.2 →
      (∀ γ ∈ nodeChains a μ, ∀ k j : ℕ, 1 ≤ k →
        ((((k : ℤ) + j - (μ.2 - a.2) : ℤ) : WithTop ℤ) ≤ (chainProd p p' r s b k j γ).orderTop) ∧
        (chainProd p p' r s b k j γ).coeff ((k : ℤ) + j - (μ.2 - a.2)) =
          chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j /
            (j.factorial : Kd)) ∧
      (∀ k j : ℕ, 1 ≤ k → k + j < μ.2 - a.2 →
        ∑ γ ∈ nodeChains a μ,
          chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j = 0) ∧
      (∀ k j : ℕ, 1 ≤ k → k + j = μ.2 - a.2 →
        (nodeChain p p' r s b a μ k j).coeff 0 =
          (∑ γ ∈ nodeChains a μ,
            chainW p p' r s b γ * chainH0 p p' r s b γ ^ (k - 1) * chainHn p p' r s b γ ^ j) /
            (j.factorial : Kd)) ∧
      (firstSteps a μ).card = μ.2 - a.2 ∧
      Set.InjOn (fun θ => nodeH p p' r s b a θ) (firstSteps a μ) ∧
      (∀ θ ∈ firstSteps a μ,
        ∑ γ ∈ (nodeChains a μ).filter (fun γ => γ.tail.head? = some θ), chainW p p' r s b γ =
          nodeTop p p' r s b a μ /
            ∏ θ' ∈ (firstSteps a μ).erase θ, (nodeH p p' r s b a θ - nodeH p p' r s b a θ'))

/-- `κ̂(a,θ,μ) = ∏_{x ∈ FS(θ→μ)} (π_x - π_a) / ∏_{x ∈ FS(a→μ) ∖ FS(a→θ)} (π_x - π_θ)`. -/
def kappaHat (a θ μ : Node) : ℚ :=
  (∏ x ∈ firstSteps θ μ, (nodePos x - nodePos a)) /
    ∏ x ∈ firstSteps a μ \ firstSteps a θ, (nodePos x - nodePos θ)

/-- Proposition 8.6 (`prop:top-ratios`).  Every `Top(x → y)` is nonzero in `K⋆`.  For
`θ ∈ FS(a→μ)`, `θ ≠ μ`:
`Top(a→θ) Top(θ→μ) = (S_θ/S_a)^{D(θ,μ)} κ̂(a,θ,μ) Top(a→μ)`.  For `ν` at even distance from `a`
with `L_a < L_ν < L_μ` the same identity holds with `(S_ν/S_a)^{D(ν,μ)}` and a rational number
`κ̂(a,ν,μ)` that depends only on the positions of the nodes. -/
def Stmt_prop_top_ratios : Prop :=
  (∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    (∀ x y : Node, x.2 < y.2 → nodeTop p p' r s b x y ≠ 0) ∧
    ∀ a θ μ : Node, θ ∈ firstSteps a μ → θ ≠ μ →
      nodeTop p p' r s b a θ * nodeTop p p' r s b θ μ =
        (((nodeS p p' r s θ : ℚ) / nodeS p p' r s a) ^ (μ.2 - θ.2) * kappaHat a θ μ : ℚ) *
          nodeTop p p' r s b a μ) ∧
  ∃ κ : Node → Node → Node → ℚ,
    ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
      ∀ a ν μ : Node, a.2 < ν.2 → ν.2 < μ.2 → (ν.2 - a.2) % 2 = 0 →
        nodeTop p p' r s b a ν * nodeTop p p' r s b ν μ =
          (((nodeS p p' r s ν : ℚ) / nodeS p p' r s a) ^ (μ.2 - ν.2) * κ a ν μ : ℚ) *
            nodeTop p p' r s b a μ

/-- Lemma 8.7 (`lem:diagonal-values`).  Let `D = D(a,μ)`.  (i) For `k + j = D`, `j ≥ 1`:
`j c^{(k)}_{a→μ,j}(b⋆) = c^{(k+1)}_{a→μ,j-1}(b⋆) - ∑_{L_ν = L_a + k} Top(a→ν) c^{(1)}_{ν→μ,j-1}(b⋆)`.
(ii) The number `f_j(a,μ) = j! (S_a/S_μ)^j c^{(D-j)}_{a→μ,j}(b⋆)/Top(a→μ)` (`0 ≤ j ≤ D-1`) is
rational, depends only on `π_a` and `π_μ`, and `f_0 = 1`. -/
def Stmt_lem_diagonal_values : Prop :=
  (∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ a μ : Node, a.2 < μ.2 → ∀ k j : ℕ, 1 ≤ k → 1 ≤ j → k + j = μ.2 - a.2 →
      (j : Kd) * (nodeChain p p' r s b a μ k j).coeff 0 =
        (nodeChain p p' r s b a μ (k + 1) (j - 1)).coeff 0 -
          ∑ ε : Bool, nodeTop p p' r s b a (ε, a.2 + k) *
            (nodeChain p p' r s b (ε, a.2 + k) μ 1 (j - 1)).coeff 0) ∧
  ∃ F : Node → Node → ℕ → ℚ, (∀ a μ : Node, F a μ 0 = 1) ∧
    ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
      ∀ a μ : Node, a.2 < μ.2 → ∀ j : ℕ, j < μ.2 - a.2 →
        (j.factorial : Kd) * (((nodeS p p' r s a : ℚ) / nodeS p p' r s μ) ^ j : ℚ) *
            (nodeChain p p' r s b a μ (μ.2 - a.2 - j) j).coeff 0 =
          (F a μ j : Kd) * nodeTop p p' r s b a μ

/-- Theorem 8.8 (`thm:diagonal`).  For nodes `a, μ` with `D = D(a,μ) ≥ 1` and `0 ≤ j ≤ D-1`,
`c^{(D-j)}_{a→μ,j}(b⋆) = f_j(L_a,D)/j! (S_μ/S_a)^j Top(a→μ)` with the closed form `fDiag`. -/
def Stmt_thm_diagonal : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ a μ : Node, a.2 < μ.2 → ∀ j : ℕ, j < μ.2 - a.2 →
      (nodeChain p p' r s b a μ (μ.2 - a.2 - j) j).coeff 0 =
        ((fDiag a.2 (μ.2 - a.2) j / j.factorial *
            ((nodeS p p' r s μ : ℚ) / nodeS p p' r s a) ^ j : ℚ) : Kd) *
          nodeTop p p' r s b a μ

/-- Corollary 8.9 (`cor:diagonal-lambda`).  In the setting of Theorem 8.2, for `L ≥ 1`,
`0 ≤ j ≤ L - 1` and each sign: `c^{(L-j)}_{λ→μ^±_L,j}(b⋆) = f_j(0,L)/j! (±m^±_L/n₀)^j N^±_L/γ^±_L`
(with `f_{2i}(0,L) = (-1)^i C(n,i)²/C(L-1,i)`, the case `l = 0` of `fDiag`); in particular, with
`w^±_2` normalized to `L_{-1}^{ℓ^±_2}`-coefficient `1`,
`γ^±_2 = ∓ (n₁/n₀) / (A_{r,s}(b⋆) A_{p±r,p'∓s}(b⋆))`. -/
def Stmt_cor_diagonal_lambda : Prop :=
  ∀ (p p' r s : ℕ) (b : ℂ), MinimalSetting p p' r s b →
    ∀ wp wm : ℕ → Verma ℂ (kacC b) (kacH r s b), TopLayerSetting p p' r s b wp wm →
      (∀ (ε : Bool) (L j : ℕ), 1 ≤ L → j < L →
        ∀ x : Nat.Partition (ellOrb p p' r s ε L) → ℂ,
          Verma.pbwCoord (ellOrb p p' r s ε L) x = (if ε then wp L else wm L) →
          (nodeChain p p' r s b (true, 0) (ε, L) (L - j) j).coeff 0 =
            ((fDiag 0 L j / j.factorial *
                ((nodeS p p' r s (ε, L) : ℚ) / nodeS p p' r s (true, 0)) ^ j : ℚ) : Kd) *
              (algebraMap ℂ[X] Kd (torusPolyForm (kacC b) (kacH r s b) x) *
                RatFunc.C (jform (kacC b) (kacH r s b) (ellOrb p p' r s ε L) L x x)⁻¹)) ∧
      (∀ (ε : Bool) (x : Nat.Partition (ellOrb p p' r s ε 2) → ℂ),
          Verma.pbwCoord (ellOrb p p' r s ε 2) x = (if ε then wp 2 else wm 2) →
          x (onesPartition (ellOrb p p' r s ε 2)) = 1 →
          jform (kacC b) (kacH r s b) (ellOrb p p' r s ε 2) 2 x x =
            (if ε then -1 else 1) * ((((p' : ℤ) * r + p * s : ℤ) : ℂ) / (((p' : ℤ) * r - p * s : ℤ) : ℂ)) /
              (genA r s b * genA (if ε then p + r else p - r) (if ε then p' - s else p' + s) b))

end Virasoro
