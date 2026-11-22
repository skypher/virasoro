import Virasoro.Proofs.Sec4Main
import Virasoro.Sphere.Proofs.Sec4ConflCore

/-!
# Sphere paper Theorem 4.7 (ii): the confluence identity over a coefficient field

`sphere/paper.tex` l.1394–1415.  Over `K(Δ)⸨t⸩`,
`H_N(c(b⋆+t),Δ,Δ_i) = ∑_λ ∑_{a ∈ C⋆_λ} B_{a,N}(t)/(Δ-λ-δ_a(t)) = ∑_λ ∑_k C_{λ,k}(t)/(Δ-λ)^k`;
the left side lies in `K(Δ)⟦t⟧` with constant term `H_N(c⋆,Δ,Δ_i)` because `det G_N` does not
vanish identically at `t = 0`; `ord_t C_{λ,k} ≥ 1` for `k > M̂⋆_{λ,N}`, and the coefficient of
`t⁰` is the identity (4.5).
-/

namespace Virasoro.Sphere

open scoped LaurentSeries
open Polynomial

section Eval

variable {𝔽 : Type} [Field 𝔽] [CharZero 𝔽]

/-- The point `(c, z, Δ₁, …, Δ₄)` of `𝔽⁶`. -/
def pt6 (c z : 𝔽) (Δe : Fin 4 → 𝔽) : Fin 6 → 𝔽 := ![c, z, Δe 0, Δe 1, Δe 2, Δe 3]

theorem eval_tau_map (c z : 𝔽) (Δe : Fin 4 → 𝔽) (Q : MvPolynomial (Fin 6) ℚ) :
    ((tau Q).map (ev5U c Δe)).eval z = MvPolynomial.aeval (pt6 c z Δe) Q := by
  have h : (evalRingHom z).comp ((mapRingHom (ev5U c Δe)).comp tau) =
      (MvPolynomial.aeval (pt6 c z Δe) : MvPolynomial (Fin 6) ℚ →ₐ[ℚ] 𝔽).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [tau, ev5U, eq_ratCast, map_ratCast]
    · intro i
      fin_cases i <;> simp [tau, ev5U, pt5U, pt6]
  exact DFunLike.congr_fun h Q

/-- The value of `H_N` at a point `z` where `det G_N(c,z) ≠ 0`, through the polynomial
`P_N ∈ ℚ[c,Δ,Δ_i]` with `H_N det G_N = P_N`. -/
theorem evalAt_Hsph_poly {Q : MvPolynomial (Fin 6) ℚ} (c z : 𝔽) (Δe : Fin 4 → 𝔽) (N : ℕ)
    (hQ : Hsph c Δe N * algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det =
      MvPolynomial.aeval (vec6U c Δe) Q)
    (hz : MvPolynomial.aeval (pt6 c z Δe) (det6 N) ≠ 0) :
    evalAt z (Hsph c Δe N) =
      MvPolynomial.aeval (pt6 c z Δe) Q / MvPolynomial.aeval (pt6 c z Δe) (det6 N) := by
  have hdet : (gramPoly c N).det = (tau (det6 N)).map (ev5U c Δe) := by
    apply IsFractionRing.injective 𝔽[X] (RatFunc 𝔽)
    rw [← aeval_vec6U, ← a6U_apply, a6U_det6]
  have hD : algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det ≠ 0 := by
    intro h0
    exact gramPoly_det_ne_zero c N
      ((map_eq_zero_iff _ (IsFractionRing.injective 𝔽[X] (RatFunc 𝔽))).mp h0)
  have hH : Hsph c Δe N = algebraMap 𝔽[X] (RatFunc 𝔽) ((tau Q).map (ev5U c Δe)) /
      algebraMap 𝔽[X] (RatFunc 𝔽) (gramPoly c N).det := by
    rw [eq_div_iff hD, hQ, aeval_vec6U]
  have hq : (gramPoly c N).det.eval z ≠ 0 := by
    rw [hdet, eval_tau_map]
    exact hz
  rw [hH, evalAt_div z _ hq, eval_tau_map]
  congr 1
  rw [hdet, eval_tau_map]

end Eval

section RegVal

variable {K : Type} [Field K] [CharZero K]

/-- A polynomial over `ℚ` in germs regular at `t = 0` is regular, with the value at the constant
terms. -/
theorem regVal_aeval {pt : Fin 6 → K⸨X⸩} {pt₀ : Fin 6 → K} (h : ∀ i, RegVal (pt i) (pt₀ i))
    (Q : MvPolynomial (Fin 6) ℚ) :
    RegVal (MvPolynomial.aeval pt Q) (MvPolynomial.aeval pt₀ Q) := by
  induction Q using MvPolynomial.induction_on with
  | C r =>
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, eq_ratCast, eq_ratCast,
      ← map_ratCast (HahnSeries.C : K →+* K⸨X⸩)]
    exact regVal_C _
  | add p q hp hq =>
    rw [map_add, map_add]
    exact hp.add hq
  | mul_X p i hp =>
    rw [map_mul, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    exact hp.mul (h i)

/-- Over `K(Δ)⸨t⸩`, the value `H_N(c(b⋆ + t), Δ, Δ_i)` is regular at `t = 0` with value
`H_N(c(b⋆), Δ, Δ_i)` (l.1402–1404). -/
theorem regVal_Hsph_germ (hK : Cited_KacDeterminant) (bs : K) (Δe : Fin 4 → K) (hbs : bs ≠ 0)
    (N : ℕ) :
    RegVal
      (evalAt (HahnSeries.C (RatFunc.X : RatFunc K))
        (Hsph (kacC (mapL (algebraMap K (RatFunc K)) (bGerm bs)))
          (fun i => mapL (algebraMap K (RatFunc K)) (HahnSeries.C (Δe i))) N))
      (Hsph (kacC bs) Δe N) := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  have hιC : ∀ x : K, ι x = RatFunc.C x := fun x => by rw [hι, RatFunc.algebraMap_eq_C]
  have hιbs : ι bs ≠ 0 := (map_ne_zero ι).2 hbs
  have hc : RegVal (kacC (mapL ι (bGerm bs))) (RatFunc.C (kacC bs)) := by
    rw [← hιC, mapL_bGerm, map_kacC]
    have hb := regVal_bGerm (ι bs)
    have hbi := hb.inv hιbs
    unfold kacC
    have h1 : RegVal (1 : (RatFunc K)⸨X⸩) 1 := by simpa using regVal_C (1 : RatFunc K)
    exact h1.add ((regVal_ofNat 6).mul ((hb.add hbi).pow 2))
  have hd : ∀ i, RegVal (mapL ι (HahnSeries.C (Δe i))) (RatFunc.C (Δe i)) := by
    intro i
    rw [mapL_C, hιC]
    exact regVal_C _
  have hpt : ∀ i, RegVal
      (pt6 (kacC (mapL ι (bGerm bs))) (HahnSeries.C (RatFunc.X : RatFunc K))
        (fun i => mapL ι (HahnSeries.C (Δe i))) i) (vec6U (kacC bs) Δe i) := by
    intro i
    fin_cases i
    · exact hc
    · exact regVal_C _
    · exact hd 0
    · exact hd 1
    · exact hd 2
    · exact hd 3
  obtain ⟨Q, hQ⟩ := isPolyFamU_Hsph_det hK N
  have hQg := hQ (RatFunc K)⸨X⸩ (kacC (mapL ι (bGerm bs)))
    (fun i => mapL ι (HahnSeries.C (Δe i)))
  have hQ0 := hQ K (kacC bs) Δe
  beta_reduce at hQg hQ0
  have hnum := regVal_aeval hpt Q
  have hden := regVal_aeval hpt (det6 N)
  have hden0 : MvPolynomial.aeval (vec6U (kacC bs) Δe) (det6 N) =
      algebraMap K[X] (RatFunc K) (gramPoly (kacC bs) N).det := by
    rw [← a6U_apply, a6U_det6]
  have hD : algebraMap K[X] (RatFunc K) (gramPoly (kacC bs) N).det ≠ 0 := by
    intro h0
    exact gramPoly_det_ne_zero (kacC bs) N
      ((map_eq_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mp h0)
  have hz : MvPolynomial.aeval (pt6 (kacC (mapL ι (bGerm bs)))
      (HahnSeries.C (RatFunc.X : RatFunc K)) (fun i => mapL ι (HahnSeries.C (Δe i))))
      (det6 N) ≠ 0 := by
    intro h0
    rw [h0] at hden
    have := hden.2
    rw [HahnSeries.coeff_zero, hden0] at this
    exact hD this.symm
  rw [evalAt_Hsph_poly _ _ _ N hQg hz]
  have hval : Hsph (kacC bs) Δe N =
      MvPolynomial.aeval (vec6U (kacC bs) Δe) Q /
        MvPolynomial.aeval (vec6U (kacC bs) Δe) (det6 N) := by
    rw [hden0, eq_div_iff hD, hQ0]
  rw [hval]
  exact hnum.div hden (by rw [hden0]; exact hD)

end RegVal

section Confluence

variable {K : Type} [Field K] [CharZero K] (bs : K) (Δe : Fin 4 → K)

theorem ordGE_BGg (N : ℕ) (a : Label) :
    OrdGE (BGg bs (RgK bs Δe) N a) (-((vhatg bs (RgK bs Δe) N a : ℕ) : ℤ)) := by
  unfold BGg vhatg
  refine ((ordGE_Rg (RgK bs Δe) a).mul (ordGE_SGg bs (RgK bs Δe) _ a)).mono ?_
  push_cast
  linarith

variable {bs}

/-- The constant term in `t` of the grouped identity. -/
theorem confluence_labels_sph (hK : Cited_KacDeterminant) (hbs : bs ≠ 0) {N : ℕ} (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      SphRecursionAtF (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (fun i => mapL (algebraMap K (RatFunc K)) (HahnSeries.C (Δe i))) M)
    (n : Label → ℕ) (hn : ∀ a ∈ labels N, vhatg bs (RgK bs Δe) N a < n a) :
    Hsph (kacC bs) Δe N =
      ∑ a ∈ labels N, ∑ j ∈ Finset.range (n a),
        RatFunc.C ((BGg bs (RgK bs Δe) N a * deltaG bs (kacHL a bs) a ^ j).coeff 0) /
          (RatFunc.X - RatFunc.C (kacHL a bs)) ^ (j + 1) := by
  set ι : K →+* RatFunc K := algebraMap K (RatFunc K) with hι
  have hsplit : ∀ a : Label, HahnSeries.C (RatFunc.X : RatFunc K) - mapL ι (hG bs a) =
      HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) -
        mapL ι (deltaG bs (kacHL a bs) a) := by
    intro a
    have h1 : mapL ι (deltaG bs (kacHL a bs) a) =
        mapL ι (hG bs a) - HahnSeries.C (RatFunc.C (kacHL a bs)) := by
      rw [deltaG, map_sub, mapL_C, hι, RatFunc.algebraMap_eq_C]
    have h2 : (HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) : (RatFunc K)⸨X⸩) =
        HahnSeries.C RatFunc.X - HahnSeries.C (RatFunc.C (kacHL a bs)) := map_sub _ _ _
    rw [h1, h2]
    ring
  have hz : ∀ a ∈ labels N, HahnSeries.C (RatFunc.X : RatFunc K) ≠ mapL ι (hG bs a) := by
    intro a _ heq
    have h0 := sub_eq_zero.2 heq
    rw [hsplit] at h0
    have hc := congrArg (fun x : (RatFunc K)⸨X⸩ => x.coeff 0) h0
    simp only [HahnSeries.coeff_sub, HahnSeries.coeff_zero] at hc
    rw [((ordGE_deltaG_one hbs a).mapL (ι := ι)).coeff_eq_zero (by norm_num), sub_zero] at hc
    have : (HahnSeries.C (RatFunc.X - RatFunc.C (kacHL a bs)) : (RatFunc K)⸨X⸩).coeff 0 =
        RatFunc.X - RatFunc.C (kacHL a bs) := (regVal_C _).2
    rw [this] at hc
    exact ratFunc_X_sub_C_ne_zero _ hc
  have hgr := grouped_at_sph bs Δe N hbs hN hrec hz
  have hreg := regVal_Hsph_germ hK bs Δe hbs N
  rw [← hι] at hreg
  rw [← hreg.2, hgr, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hsplit]
  have hlt : (0 : ℤ) < -((vhatg bs (RgK bs Δe) N a : ℕ) : ℤ) + (n a : ℕ) := by
    have := hn a ha
    have : ((vhatg bs (RgK bs Δe) N a : ℕ) : ℤ) < (n a : ℕ) := by exact_mod_cast this
    linarith
  rw [pole_support ι _ (ratFunc_X_sub_C_ne_zero _) _ _ (ordGE_deltaG_one hbs a)
    (ordGE_BGg bs Δe N a) 0 (n a) hlt]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hι, RatFunc.algebraMap_eq_C]

/-- The collision moments vanish beyond the a priori pole bound (l.1400–1401). -/
theorem Atildeg_eq_zero (hbs : bs ≠ 0) (N : ℕ) (lam : K) {k : ℕ}
    (hk : Mhatg bs (RgK bs Δe) N lam < k) : Atildeg bs (RgK bs Δe) N lam k = 0 := by
  classical
  unfold Atildeg
  rw [HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro a ha
  have hlam : kacHL a bs = lam := (mem_collClass.1 ha).2
  have hle : (if deltaG bs lam a = 0 then 1
      else 1 + vhatg bs (RgK bs Δe) N a / ((deltaG bs lam a).order).toNat) ≤
        Mhatg bs (RgK bs Δe) N lam :=
    Finset.le_sup (f := fun a => if deltaG bs lam a = 0 then 1
      else 1 + vhatg bs (RgK bs Δe) N a / ((deltaG bs lam a).order).toNat) ha
  by_cases h0 : deltaG bs lam a = 0
  · rw [if_pos h0] at hle
    rw [h0, zero_pow (by omega), mul_zero, HahnSeries.coeff_zero]
  · rw [if_neg h0] at hle
    have hδ1 : OrdGE (deltaG bs lam a) 1 := by rw [← hlam]; exact ordGE_deltaG_one hbs a
    have hord1 : 1 ≤ (deltaG bs lam a).order := by
      have := hδ1
      unfold OrdGE at this
      rw [← HahnSeries.order_eq_orderTop_of_ne_zero h0] at this
      exact_mod_cast this
    set ε := ((deltaG bs lam a).order).toNat with hε
    have hεpos : 0 < ε := by omega
    have hεeq : (ε : ℤ) = (deltaG bs lam a).order := Int.toNat_of_nonneg (by omega)
    have hpow : OrdGE (deltaG bs lam a ^ (k - 1)) (((k - 1 : ℕ) : ℤ) * (ε : ℤ)) := by
      rw [hεeq]
      exact (ordGE_order _).pow (k - 1)
    have hprod := (ordGE_BGg bs Δe N a).mul hpow
    apply hprod.coeff_eq_zero
    have hdiv : vhatg bs (RgK bs Δe) N a / ε < k - 1 := by omega
    have hlt : vhatg bs (RgK bs Δe) N a < (k - 1) * ε := (Nat.div_lt_iff_lt_mul hεpos).1 hdiv
    have : ((vhatg bs (RgK bs Δe) N a : ℕ) : ℤ) < ((k - 1 : ℕ) : ℤ) * (ε : ℤ) := by
      exact_mod_cast hlt
    linarith

open Classical in
/-- The confluence identity (4.5) over an arbitrary coefficient field. -/
theorem confluence_identity_sph (hK : Cited_KacDeterminant) (hbs : bs ≠ 0) {N : ℕ}
    (hN : 1 ≤ N)
    (hrec : ∀ M, 1 ≤ M → M ≤ N →
      SphRecursionAtF (mapL (algebraMap K (RatFunc K)) (bGerm bs))
        (fun i => mapL (algebraMap K (RatFunc K)) (HahnSeries.C (Δe i))) M) :
    Hsph (kacC bs) Δe N =
      ∑ lam ∈ Lam N bs, ∑ k ∈ Finset.Icc 1 (Mhatg bs (RgK bs Δe) N lam),
        RatFunc.C (Atildeg bs (RgK bs Δe) N lam k) / (RatFunc.X - RatFunc.C lam) ^ k := by
  set n₀ : ℕ := (labels N).sup (fun a => vhatg bs (RgK bs Δe) N a) +
    (Lam N bs).sup (fun lam => Mhatg bs (RgK bs Δe) N lam) + 1 with hn₀
  have hn : ∀ a ∈ labels N, vhatg bs (RgK bs Δe) N a < n₀ := by
    intro a ha
    have := Finset.le_sup (f := fun a => vhatg bs (RgK bs Δe) N a) ha
    omega
  rw [confluence_labels_sph Δe hK hbs hN hrec (fun _ => n₀) hn]
  have hmaps : ∀ a ∈ labels N, kacHL a bs ∈ Lam N bs := fun a ha =>
    Finset.mem_image_of_mem _ ha
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  have hcl : ((labels N).filter fun a => kacHL a bs = lam) = collClass N bs lam := rfl
  rw [hcl]
  have hstep : ∑ a ∈ collClass N bs lam, ∑ j ∈ Finset.range n₀,
        RatFunc.C ((BGg bs (RgK bs Δe) N a * deltaG bs (kacHL a bs) a ^ j).coeff 0) /
          (RatFunc.X - RatFunc.C (kacHL a bs)) ^ (j + 1) =
      ∑ j ∈ Finset.range n₀, RatFunc.C (Atildeg bs (RgK bs Δe) N lam (j + 1)) /
        (RatFunc.X - RatFunc.C lam) ^ (j + 1) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold Atildeg
    rw [HahnSeries.coeff_sum, map_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [(mem_collClass.1 ha).2, Nat.add_sub_cancel]
  rw [hstep, sum_range_succ_eq_Icc
    (fun k => RatFunc.C (Atildeg bs (RgK bs Δe) N lam k) / (RatFunc.X - RatFunc.C lam) ^ k) n₀]
  symm
  have hMle : Mhatg bs (RgK bs Δe) N lam ≤ n₀ := by
    have := Finset.le_sup (f := fun lam => Mhatg bs (RgK bs Δe) N lam) hlam
    omega
  apply Finset.sum_subset (Finset.Icc_subset_Icc_right hMle)
  intro k hk hk'
  have hgt : Mhatg bs (RgK bs Δe) N lam < k := by
    simp only [Finset.mem_Icc, not_and, not_le] at hk hk'
    exact hk' hk.1
  rw [Atildeg_eq_zero Δe hbs N lam hgt, map_zero, zero_div]

end Confluence

end Virasoro.Sphere
