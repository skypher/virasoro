import Virasoro.Proofs.P2Sec11VertexForm

/-!
# Proposition 11.2(i), induction step: `J^{i+1} ⊂ rad ρ^{(i)}` for `i ≥ 1` (paper.tex l.2439–2459)

For a form `ρ` on a `Vir`-submodule `J = U(Vir_-)χ⁺ + U(Vir_-)χ⁻` of `M(c,μ)` that satisfies the
`V_d(1)` Ward identity:
* on each Verma submodule `M(μ^ε) = U(Vir_-)χ^ε` the Ward identity forces
  `ρ = ρ(χ^ε,χ^ε) ρ_{c,μ^ε,d}` (l.2443–2447);
* a singular vector `a` of `M(μ^ε)` with `ρ_{c,μ^ε,d}(a, v_{μ^ε}) = 0` has `ρ(a,χ^ε) = 0`
  (l.2447–2453);
* Ward induction on the descendants of `χ^±` gives `ρ(a, J) = 0`, and a second Ward induction
  gives `ρ(U(Vir_-)a, J) = 0` (l.2454–2458).
-/

namespace Virasoro

open Verma

variable {c μ d : ℂ}

/-- A symmetric form on a `Vir`-submodule `J ⊂ M(c,μ)`, bilinear on `J`, with the `V_d(1)` Ward
identity (10.1) on `J`. -/
structure IsJWard (d : ℂ) (J : Submodule ℂ (Verma ℂ c μ))
    (R : Verma ℂ c μ → Verma ℂ c μ → ℂ) : Prop where
  add_left : ∀ {x x' y}, x ∈ J → x' ∈ J → y ∈ J → R (x + x') y = R x y + R x' y
  smul_left : ∀ (a : ℂ) {x y}, x ∈ J → y ∈ J → R (a • x) y = a * R x y
  symm : ∀ x y, R x y = R y x
  ward : ∀ (n : ℤ) {x y}, x ∈ J → y ∈ J →
    R (L (-n) x) y - R x (L n y) = R (L 0 x) y - R x (L 0 y) + (n : ℂ) * d * R x y
  stable : ∀ (n : ℤ) {x}, x ∈ J → L n x ∈ J

namespace IsJWard

variable {J : Submodule ℂ (Verma ℂ c μ)} {R : Verma ℂ c μ → Verma ℂ c μ → ℂ}

theorem zero_left (hR : IsJWard d J R) {y : Verma ℂ c μ} (hy : y ∈ J) : R 0 y = 0 := by
  have h := hR.add_left J.zero_mem J.zero_mem hy
  have e : (0 : Verma ℂ c μ) + 0 = 0 := add_zero 0
  rw [e] at h
  linear_combination -h

theorem add_right (hR : IsJWard d J R) {x y y' : Verma ℂ c μ} (hx : x ∈ J) (hy : y ∈ J)
    (hy' : y' ∈ J) : R x (y + y') = R x y + R x y' := by
  rw [hR.symm, hR.add_left hy hy' hx, hR.symm y, hR.symm y']

theorem smul_right (hR : IsJWard d J R) (a : ℂ) {x y : Verma ℂ c μ} (hx : x ∈ J) (hy : y ∈ J) :
    R x (a • y) = a * R x y := by
  rw [hR.symm, hR.smul_left a hy hx, hR.symm y]

/-- The restriction of the form to the image of a homomorphism `M(c,h') → J`. -/
theorem pullback (hR : IsJWard d J R) {h' : ℂ} (j : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c μ)
    (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v)) (hjJ : ∀ v, j v ∈ J) :
    ∃ η : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c h' →ₗ[ℂ] ℂ,
      (∀ u v, η u v = R (j u) (j v)) ∧ IsWardPairing d η := by
  let η : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c h' →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun u v => R (j u) (j v))
      (fun u u' v => by rw [map_add, hR.add_left (hjJ u) (hjJ u') (hjJ v)])
      (fun a u v => by rw [map_smul, hR.smul_left a (hjJ u) (hjJ v), smul_eq_mul])
      (fun u v v' => by rw [map_add, hR.add_right (hjJ u) (hjJ v) (hjJ v')])
      (fun a u v => by rw [map_smul, hR.smul_right a (hjJ u) (hjJ v), smul_eq_mul])
  have hη : ∀ u v, η u v = R (j u) (j v) := fun u v => rfl
  refine ⟨η, hη, fun n u v => ?_⟩
  rw [hη, hη, hη, hη, hη, hjL, hjL, hjL, hjL]
  exact hR.ward n (hjJ u) (hjJ v)

/-- First Ward induction (l.2454–2456): for `L_n a = 0` (`n > 0`), `L_0 a = λ a` and
`ρ(a, χ) = 0`, `ρ(a, U(Vir_-)χ) = 0`. -/
theorem right_zero (hR : IsJWard d J R) {a : Verma ℂ c μ} (haJ : a ∈ J) {lam : ℂ}
    (ha0 : L 0 a = lam • a) (hapos : ∀ n : ℤ, 0 < n → L n a = 0) {h' : ℂ}
    (j : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c μ) (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v))
    (hjJ : ∀ v, j v ∈ J) (h0 : R a (j hw) = 0) : ∀ v, R a (j v) = 0 := by
  refine induction_neg (fun w hw => ?_)
    (fun u v hu hv => by rw [map_add, hR.add_right haJ (hjJ u) (hjJ v), hu, hv, add_zero])
    (fun r v hv => by rw [map_smul, hR.smul_right r haJ (hjJ v), hv, mul_zero])
  induction w with
  | nil => rw [neg_nil]; exact h0
  | cons m w ih =>
    have hm : 0 < m := hw m List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have e := hR.ward (-(m : ℤ)) haJ (hjJ (neg w))
    have e1 : R (L (m : ℤ) a) (j (neg w)) = 0 := by
      rw [hapos _ (by exact_mod_cast hm)]
      exact hR.zero_left (hjJ _)
    have e2 : L (-(m : ℤ)) (j (neg w)) = j (neg (m :: w)) := by rw [← hjL, ← neg_cons]
    have e3 : R (L 0 a) (j (neg w)) = 0 := by
      rw [ha0, hR.smul_left _ haJ (hjJ _), ih hw', mul_zero]
    have e4 : R a (L 0 (j (neg w))) = 0 := by
      rw [← hjL, L_zero_neg, map_smul, hR.smul_right _ haJ (hjJ _), ih hw', mul_zero]
    rw [neg_neg, e1, e2, e3, e4, ih hw'] at e
    linear_combination -e

/-- Second Ward induction (l.2456–2458): if `ρ(a, J) = 0` then `ρ(U(Vir_-)a, J) = 0`. -/
theorem left_zero (hR : IsJWard d J R) {h' : ℂ} (j : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c μ)
    (hjL : ∀ (n : ℤ) v, j (L n v) = L n (j v)) (hjJ : ∀ v, j v ∈ J)
    (h0 : ∀ y ∈ J, R (j hw) y = 0) : ∀ v, ∀ y ∈ J, R (j v) y = 0 := by
  refine induction_neg (fun w hw => ?_)
    (fun u v hu hv y hy => by
      rw [map_add, hR.add_left (hjJ u) (hjJ v) hy, hu y hy, hv y hy, add_zero])
    (fun r v hv y hy => by rw [map_smul, hR.smul_left r (hjJ v) hy, hv y hy, mul_zero])
  induction w with
  | nil => rw [neg_nil]; exact h0
  | cons m w ih =>
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    intro y hy
    have e := hR.ward (m : ℤ) (hjJ (neg w)) hy
    have e2 : L (-(m : ℤ)) (j (neg w)) = j (neg (m :: w)) := by rw [← hjL, ← neg_cons]
    have e3 : R (L 0 (j (neg w))) y = 0 := by
      rw [← hjL, L_zero_neg, map_smul, hR.smul_left _ (hjJ _) hy, ih hw' y hy, mul_zero]
    rw [e2, e3, ih hw' _ (hR.stable _ hy), ih hw' _ (hR.stable _ hy), ih hw' y hy] at e
    linear_combination e

end IsJWard

/-- "The Ward identity and Lemma 10.1 force the restriction to equal `σ ρ_{c,μ^ε,d}`"
(l.2443–2447): a form on `M(c,h')` with the Ward identity is its value on the highest-weight
vector times the primary pairing. -/
theorem ward_eq_smul_pairing {c h' d : ℂ} {η : Verma ℂ c h' →ₗ[ℂ] Verma ℂ c h' →ₗ[ℂ] ℂ}
    (hη : IsWardPairing d η) (u v : Verma ℂ c h') :
    η u v = η hw hw * pairing c h' d u v := by
  have e : η = (η hw hw) • pairing c h' d :=
    linearMap_ext fun Y hY => linearMap_ext fun w hw => by
      rw [ward_torusWord hη Y hY w hw, LinearMap.smul_apply, LinearMap.smul_apply,
        primary_torusWord (isPrimaryPairing_pairing d) Y hY w hw, smul_eq_mul]
  conv_lhs => rw [e]
  rfl

theorem mem_negSpan_self {c h : ℂ} (χ : Verma ℂ c h) : χ ∈ negSpan χ :=
  Submodule.subset_span ⟨[], by simp [VirEnv.negOp]⟩

namespace IsJWard

variable {J : Submodule ℂ (Verma ℂ c μ)} {R : Verma ℂ c μ → Verma ℂ c μ → ℂ}

/-- A singular vector `a` of the Verma submodule `U(Vir_-)χ ≅ M(c,μ+ℓ)` whose preimage pairs to
zero with the highest-weight vector under `ρ_{c,μ+ℓ,d}` has `ρ(a,χ) = 0` (l.2447–2453). -/
theorem sing_zero (hI : Cited_VermaHomInjective) (hR : IsJWard d J R) {χ : Verma ℂ c μ} {ℓ : ℕ}
    (hχ : IsSingular χ ℓ) (hsub : negSpan χ ≤ J) {a : Verma ℂ c μ} {N : ℕ}
    (ha : IsSingular a N) (haχ : a ∈ negSpan χ)
    (hpair : ∀ u : Verma ℂ c (μ + ℓ), IsSingular u (N - ℓ) → pairing c (μ + ℓ) d u hw = 0) :
    R a χ = 0 := by
  have hle := (singular_pullback hI hχ haχ ha).1
  obtain ⟨j, hinj, hjhw, hjL, hjr, -, hjneg⟩ := exists_emb hI hχ
  rw [negSpan_eq_range j hjneg] at haχ
  obtain ⟨u, rfl⟩ := haχ
  have hu : IsSingular u (N - ℓ) := by
    refine ⟨fun h0 => ha.1 (by rw [h0, map_zero]), hinj ?_, fun n hn => hinj ?_⟩
    · rw [hjL, ha.2.1, map_smul]
      congr 1
      rw [Nat.cast_sub hle]
      ring
    · rw [hjL, ha.2.2 n hn, map_zero]
  obtain ⟨η, hη, hW⟩ := hR.pullback j hjL fun v => hsub (hjr v)
  have h1 := ward_eq_smul_pairing hW u hw
  rw [hpair u hu, mul_zero, hη, hjhw] at h1
  exact h1

/-- `J' = U(Vir_-)a⁺ + U(Vir_-)a⁻ ⊂ rad ρ` when `J = U(Vir_-)χ⁺ + U(Vir_-)χ⁻` and
`ρ(a^η, χ^ε) = 0` for the four pairs (l.2454–2458). -/
theorem radical (hR : IsJWard d J R) {χp χm ap am : Verma ℂ c μ} {ℓp ℓm Np Nm : ℕ}
    (hχp : IsSingular χp ℓp) (hχm : IsSingular χm ℓm) (hJ : J = negSpan χp ⊔ negSpan χm)
    (hap : IsSingular ap Np) (ham : IsSingular am Nm) (hsp : negSpan ap ≤ J)
    (hsm : negSpan am ≤ J) (hpp : R ap χp = 0) (hpm : R ap χm = 0) (hmp : R am χp = 0)
    (hmm : R am χm = 0) : ∀ x ∈ negSpan ap ⊔ negSpan am, ∀ y ∈ J, R x y = 0 := by
  obtain ⟨jp, hjp, hjpL, hjpn⟩ := exists_singularHom hχp.2.1 hχp.2.2
  obtain ⟨jm, hjm, hjmL, hjmn⟩ := exists_singularHom hχm.2.1 hχm.2.2
  obtain ⟨kp, hkp, hkpL, hkpn⟩ := exists_singularHom hap.2.1 hap.2.2
  obtain ⟨km, hkm, hkmL, hkmn⟩ := exists_singularHom ham.2.1 ham.2.2
  have rjp := negSpan_eq_range jp hjpn
  have rjm := negSpan_eq_range jm hjmn
  have rkp := negSpan_eq_range kp hkpn
  have rkm := negSpan_eq_range km hkmn
  have hjpJ : ∀ v, jp v ∈ J := fun v => by
    rw [hJ]; exact Submodule.mem_sup_left (rjp ▸ ⟨v, rfl⟩)
  have hjmJ : ∀ v, jm v ∈ J := fun v => by
    rw [hJ]; exact Submodule.mem_sup_right (rjm ▸ ⟨v, rfl⟩)
  have hkpJ : ∀ v, kp v ∈ J := fun v => hsp (rkp ▸ ⟨v, rfl⟩)
  have hkmJ : ∀ v, km v ∈ J := fun v => hsm (rkm ▸ ⟨v, rfl⟩)
  have one : ∀ {a : Verma ℂ c μ} {N : ℕ}, IsSingular a N → a ∈ J → R a χp = 0 → R a χm = 0 →
      ∀ y ∈ J, R a y = 0 := by
    intro a N ha haJ h1 h2 y hy
    have z1 := hR.right_zero haJ ha.2.1 ha.2.2 jp hjpL hjpJ (by rw [hjp]; exact h1)
    have z2 := hR.right_zero haJ ha.2.1 ha.2.2 jm hjmL hjmJ (by rw [hjm]; exact h2)
    rw [hJ, Submodule.mem_sup] at hy
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := hy
    rw [rjp] at hy₁
    rw [rjm] at hy₂
    obtain ⟨v₁, rfl⟩ := hy₁
    obtain ⟨v₂, rfl⟩ := hy₂
    rw [hR.add_right haJ (hjpJ _) (hjmJ _), z1, z2, add_zero]
  have zp := hR.left_zero kp hkpL hkpJ (by
    rw [hkp]; exact one hap (hsp (mem_negSpan_self ap)) hpp hpm)
  have zm := hR.left_zero km hkmL hkmJ (by
    rw [hkm]; exact one ham (hsm (mem_negSpan_self am)) hmp hmm)
  intro x hx y hy
  rw [Submodule.mem_sup] at hx
  obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hx
  rw [rkp] at hx₁
  rw [rkm] at hx₂
  obtain ⟨v₁, rfl⟩ := hx₁
  obtain ⟨v₂, rfl⟩ := hx₂
  rw [hR.add_left (hkpJ _) (hkmJ _) hy, zp v₁ y hy, zm v₂ y hy, add_zero]

end IsJWard

end Virasoro
