import Virasoro.Sphere.Proofs.Sec6Examples
import Virasoro.Proofs.Sec6TTVal
import Virasoro.Proofs.Sec6LayerFinal
import Virasoro.Proofs.Sec5Jantzen
import Virasoro.Proofs.Sec3

/-!
# Propositions 6.1 and 6.2 of `sphere/paper.tex`

`prop:c0-example` (sphere/paper.tex l.1792–1810) and `prop:ising-example` (l.1812–1832), with the
proof at l.1834–1859.  At `N = ℓ₂` the first double pole comes from the single term `M = 0` of
Theorem 5.4 of the sphere paper (`fdp_minus`, `fdp_plus`).  The norms `γ`:

* `(2,3)`, `λ = 0`: by the proof of the torus Proposition 6.9, `τ⁻_2 = 𝒫_{1,1} 𝒫_{1,4}`, with
  `[d²]τ⁻_2 = 2800/3`; by the torus Proposition 6.7, `[d²](τ⁻_2/γ₅) = c₂ ρ² = -1/4`
  (l.1843–1849);
* Ising: the three norms of the torus Proposition 8.1 (l.1840–1842), transported by the
  uniqueness of the normalized singular vector.
-/

namespace Virasoro

namespace TT

open Polynomial

theorem facs_c0 : facs 2 3 1 1 false 2 = [(1, 1), (1, 4)] := by decide

theorem idx11 : idx 1 1 = {((1, 1), true), ((1, 1), false)} := by decide

theorem idx14 : idx 1 4 = {((1, 1), true), ((1, 1), false), ((1, 3), true), ((1, 3), false),
    ((1, 5), true), ((1, 5), false), ((1, 7), true), ((1, 7), false)} := by decide

/-- `d = 0` is a root of multiplicity two of `𝒫_{1,1} 𝒫_{1,4}` at `(2,3)` (`x = 1` twice). -/
theorem cnt_c0 : ((facs 2 3 1 1 false 2).map (cnt 2 3 0)).sum = 2 := by
  rw [facs_c0]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, cnt, idx11, idx14]
  simp [Finset.filter_insert, Finset.filter_singleton, xv, dQ]
  norm_num

/-- The product of the remaining roots: `1 · 1 · 1/3 · 10/3 · 2 · 7 · 5 · 12 = 2800/3`
(sphere/paper.tex l.1845–1847). -/
theorem cof_c0 : ((facs 2 3 1 1 false 2).map (cof 2 3 0)).prod = 2800 / 3 := by
  rw [facs_c0]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, cof, idx11, idx14]
  simp [Finset.filter_insert, Finset.filter_singleton, xv, dQ]
  norm_num

/-- `[d²]τ⁻_2 = 2800/3` at `(p,p',r,s) = (2,3,1,1)` (sphere/paper.tex l.1843–1847). -/
theorem tau_c0 : (tauQ 2 3 1 1 false 2).coeff 2 = 2800 / 3 := by
  rw [tauQ_eq_facs]
  have hs := splitAt_prodPQ 2 3 0 (facs 2 3 1 1 false 2)
  rw [cnt_c0] at hs
  rw [coeff_split0 hs, eval_cofP_prod, cnt_c0, cof_c0]
  norm_num

end TT

namespace Sphere

variable {p p' r s : ℕ}

/-- Two singular vectors of the same level with `L_{-1}^n`-coefficient `1` are equal (cited
uniqueness of singular vectors). -/
theorem normalized_eq (hU : Cited_SingularUnique) {c h : ℂ} {n : ℕ} {x₀ xt : Nat.Partition n → ℂ}
    (h0 : x₀ (onesPartition n) = 1)
    (hs0 : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) n x₀) n)
    (h1 : xt (onesPartition n) = 1)
    (hs1 : Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) n xt) n) : xt = x₀ := by
  obtain ⟨a, ha⟩ := hU _ _ _ _ _ hs0 hs1
  have hxa : xt = a • x₀ := Verma.pbwCoord_injective _ (by rw [ha, map_smul])
  have ha1 : a = 1 := by
    have := congrFun hxa (onesPartition n)
    rw [Pi.smul_apply, h0, h1, smul_eq_mul, mul_one] at this
    exact this.symm
  rw [hxa, ha1, one_smul]

/-- Transport of the norm of the normalized singular vector along equalities of the charge, the
weight and the level. -/
theorem gamma_transfer (hU : Cited_SingularUnique) {c h c' h' : ℂ} {n n' : ℕ} (hc : c = c')
    (hh : h = h') (hn : n = n') {x₀ : Nat.Partition n' → ℂ} (h0 : x₀ (onesPartition n') = 1)
    (hs0 : Verma.IsSingular (Verma.pbwCoord (c := c') (h := h') n' x₀) n') {γ : ℂ}
    (hj : jform c' h' n' 2 x₀ x₀ = γ) :
    ∀ xt : Nat.Partition n → ℂ, xt (onesPartition n) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := c) (h := h) n xt) n → jform c h n 2 xt xt = γ := by
  subst hc hh hn
  intro xt h1 hs
  rw [normalized_eq hU h0 hs0 h1 hs, hj]

/-- The torus Proposition 6.7 for the normalized `w⁻_k`: `B^k(w,w) c_k (-ρ)^k = [d^k]τ⁻_k`. -/
theorem jform_norm_minus (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations) (hU : Cited_SingularUnique)
    {b : ℂ} (hset : MinimalSetting p p' r s b) {k : ℕ} (hk : 1 ≤ k)
    (xt : Nat.Partition (ellMinus p p' r s k) → ℂ) (hx1 : xt (onesPartition _) = 1)
    (hxs : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b)
      (ellMinus p p' r s k) xt) (ellMinus p p' r s k)) :
    jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xt xt * (layerConst k : ℂ) *
        (-(-((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p)))) ^ k =
      ((TT.tauQ p p' r s false k).coeff k : ℂ) := by
  obtain ⟨hp, hp', hcop, hr, hrp, hs, hsp, hlt, hb⟩ := id hset
  obtain ⟨wp, wm, hsing, hjan, -, -⟩ :=
    thm_jantzen_smith hJ p p' r s hp hp' hcop hr hrp hs hsp hlt b hb
  have hT : TopLayerSetting p p' r s b wp wm := ⟨hsing, hjan⟩
  obtain ⟨xm, hxm_def⟩ : ∃ xm, xm = Verma.comp (ellMinus p p' r s k) (wm k) := ⟨_, rfl⟩
  have hcm : Verma.pbwCoord (ellMinus p p' r s k) xm = wm k := by
    rw [hxm_def]
    exact Verma.pbwCoord_comp_of_mem_level (Verma.mem_level_of_L_zero (hsing k hk).2.2.1)
  have hsm : Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH r s b)
      (ellMinus p p' r s k) xm) (ellMinus p p' r s k) := by
    rw [hcm]; exact (hsing k hk).2
  obtain ⟨-, l67m⟩ := prop_layer_coefficients_of_cited hI hK hH p p' r s b hset wp wm hT k hk
  obtain ⟨-, lmk, lmne⟩ := l67m xm hcm
  have hlev := TT.ellOrb_pos hp hp' hr hrp hs hsp false hk
  rw [TT.ellOrb_false hk] at hlev
  have hτm := TT.tau_norm hH hU hset false hk (TT.ellOrb_false hk) hlev xm hsm
  rw [TT.coeff_tau_norm hτm] at lmk lmne
  obtain ⟨a, ha⟩ := hU _ _ _ _ _ hxs hsm
  have hxa : xm = a • xt := Verma.pbwCoord_injective _ (by rw [ha, map_smul])
  have ha1 : xm (onesPartition _) = a := by
    rw [hxa, Pi.smul_apply, hx1, smul_eq_mul, mul_one]
  rw [ha1] at lmk lmne
  have ha0 : a ≠ 0 := by
    intro h0; apply lmne; rw [h0]; ring
  have hjm : jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xm xm ≠ 0 := by
    intro h0; apply lmne; rw [lmk, h0]; ring
  have hmem : xt ∈ jantzenLayer (kacC b) (kacH r s b) (ellMinus p p' r s k) k := by
    have h2 : xt = a⁻¹ • xm := by rw [hxa, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (mem_layer_of_jform_ne hjm)
  rw [hxa, jform_smul_smul a hmem] at lmk
  have key : a ^ 2 * (jform (kacC b) (kacH r s b) (ellMinus p p' r s k) k xt xt *
      (layerConst k : ℂ) * (-(-((p' : ℂ) * r - (p : ℂ) * s) / (2 * ((p' : ℂ) - p)))) ^ k) =
      a ^ 2 * ((TT.tauQ p p' r s false k).coeff k : ℂ) := by
    rw [lmk]; ring
  exact mul_left_cancel₀ (pow_ne_zero 2 ha0) key

/-- Proposition 6.1 (sphere/paper.tex l.1792–1810, proof l.1834–1849).
Paper label: prop:c0-example -/
theorem prop_c0_example_of_cited (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hF : Cited_SphereFusionPolynomial) (hU : Cited_SingularUnique) :
    Stmt_prop_c0_example := by
  intro b hb
  have hset : MinimalSetting 2 3 1 1 b := ⟨le_rfl, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, by rw [hb]; push_cast; ring⟩
  have hc : kacC b = 0 := by
    rw [kacC_minimal 2 3 (by norm_num) (by norm_num) b hb]; norm_num
  have hh : kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b = 0 := by
    rw [Virasoro.kacH_min' hset]; push_cast; norm_num
  have hl1p : ellPlus 2 3 1 1 1 = 1 := by decide
  have hl1m : ellMinus 2 3 1 1 1 = 2 := by decide
  have hl2m : ellMinus 2 3 1 1 2 = 5 := by decide
  have hl2p : ellPlus 2 3 1 1 2 = 7 := by decide
  have hγ : ∀ xt : Nat.Partition (ellMinus 2 3 1 1 2) → ℂ, xt (onesPartition _) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b)
        (ellMinus 2 3 1 1 2) xt) (ellMinus 2 3 1 1 2) →
      jform (kacC b) (kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b) (ellMinus 2 3 1 1 2) 2 xt xt =
        -11200 / 3 := by
    intro xt h1 hs
    have h := jform_norm_minus hJ hI hK hH hU hset (k := 2) (by norm_num) xt h1 hs
    rw [TT.tau_c0] at h
    have hL : (layerConst 2 : ℂ) = -1 := by norm_num [layerConst]
    rw [hL] at h
    push_cast at h
    linear_combination (-4 : ℂ) * h
  have hf := fdp_minus hJ hI hH hF hU hset (by decide) hγ
  rw [hc, hh, hl2m] at hf
  refine ⟨hc, by simpa using hh, hl1p, hl1m, hl2m, hl2p, hf⟩

/-- Proposition 6.2 (sphere/paper.tex l.1812–1832, proof l.1834–1842).
Paper label: prop:ising-example -/
theorem prop_ising_example_of_cited (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective)
    (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    (hF : Cited_SphereFusionPolynomial) (hU : Cited_SingularUnique) :
    Stmt_prop_ising_example := by
  intro b hb
  have hb' : b ^ 2 = -((4 : ℕ) : ℂ) / ((3 : ℕ) : ℂ) := by rw [hb]; push_cast; ring
  have hs1 : MinimalSetting 3 4 2 1 b := ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, hb'⟩
  have hs2 : MinimalSetting 3 4 1 2 b := ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, hb'⟩
  have hs3 : MinimalSetting 3 4 1 1 b := ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num, hb'⟩
  have hc : kacC b = 1 / 2 := by
    rw [kacC_minimal 3 4 (by norm_num) (by norm_num) b hb]; norm_num
  have hh1 : kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b = 1 / 2 := by
    rw [Virasoro.kacH_min' hs1]; push_cast; norm_num
  have hh2 : kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b = 1 / 16 := by
    rw [Virasoro.kacH_min' hs2]; push_cast; norm_num
  have hh3 : kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b = 0 := by
    rw [Virasoro.kacH_min' hs3]; push_cast; norm_num
  have hl1 : ellMinus 3 4 2 1 2 = 7 := by decide
  have hl2 : ellPlus 3 4 1 2 2 = 10 := by decide
  have hl3 : ellMinus 3 4 1 1 2 = 11 := by decide
  obtain ⟨-, R1, R2, R3⟩ := prop_ising_double_poles_of_cited hK hH hJ hI hU
  obtain ⟨-, -, -, x₁, h11, hx₁, -, hj₁⟩ := R1
  obtain ⟨-, -, -, x₂, h12, hx₂, -, hj₂⟩ := R2
  obtain ⟨-, -, -, x₃, h13, hx₃, -, hj₃⟩ := R3
  have hγ1 : ∀ xt : Nat.Partition (ellMinus 3 4 2 1 2) → ℂ, xt (onesPartition _) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b)
        (ellMinus 3 4 2 1 2) xt) (ellMinus 3 4 2 1 2) →
      jform (kacC b) (kacH ((2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b) (ellMinus 3 4 2 1 2) 2 xt xt =
        -700700 := by
    exact gamma_transfer hU hc hh1 hl1 h11 hx₁ hj₁
  have hγ2 : ∀ xt : Nat.Partition (ellPlus 3 4 1 2 2) → ℂ, xt (onesPartition _) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b)
        (ellPlus 3 4 1 2 2) xt) (ellPlus 3 4 1 2 2) →
      jform (kacC b) (kacH ((1 : ℕ) : ℤ) ((2 : ℕ) : ℤ) b) (ellPlus 3 4 1 2 2) 2 xt xt =
        -1121229484375 / 192 := by
    exact gamma_transfer (n' := 10) (c' := 1 / 2) (h' := 1 / 16) (x₀ := x₂)
      (γ := -1121229484375 / 192) hU hc hh2 hl2 h12 (by convert hx₂ using 0)
      (by convert hj₂ using 0)
  have hγ3 : ∀ xt : Nat.Partition (ellMinus 3 4 1 1 2) → ℂ, xt (onesPartition _) = 1 →
      Verma.IsSingular (Verma.pbwCoord (c := kacC b) (h := kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b)
        (ellMinus 3 4 1 1 2) xt) (ellMinus 3 4 1 1 2) →
      jform (kacC b) (kacH ((1 : ℕ) : ℤ) ((1 : ℕ) : ℤ) b) (ellMinus 3 4 1 1 2) 2 xt xt =
        -2477917160468750 / 6561 := by
    exact gamma_transfer (n' := 11) (c' := 1 / 2) (h' := 0) (x₀ := x₃)
      (γ := -2477917160468750 / 6561) hU hc hh3 hl3 h13 (by convert hx₃ using 0)
      (by convert hj₃ using 0)
  have hf1 := fdp_minus hJ hI hH hF hU hs1 (by decide) hγ1
  have hf2 := fdp_plus hJ hI hH hF hU hs2 (by decide) hγ2
  have hf3 := fdp_minus hJ hI hH hF hU hs3 (by decide) hγ3
  rw [hc, hh1, hl1] at hf1
  rw [hc, hh2, hl2] at hf2
  rw [hc, hh3, hl3] at hf3
  exact ⟨hc, hf1, hf2, hf3⟩

example (hJ : Cited_JantzenLayers) (hI : Cited_VermaHomInjective) (hK : Cited_KacDeterminant)
    (hH : Cited_HJSNormalizations) (hF : Cited_SphereFusionPolynomial)
    (hU : Cited_SingularUnique) : Stmt_prop_c0_example ∧ Stmt_prop_ising_example :=
  ⟨prop_c0_example_of_cited hJ hI hK hH hF hU, prop_ising_example_of_cited hJ hI hK hH hF hU⟩

end Sphere

end Virasoro
