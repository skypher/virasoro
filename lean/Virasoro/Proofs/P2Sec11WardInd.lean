import Virasoro.Statements.Sec11b
import Virasoro.Proofs.VermaSpan

/-!
# The Ward-induction fact of the proof of Proposition 11.2 (paper.tex l.2401–2410)

If a symmetric bilinear form `η` on a Verma module `M(c,ν)` satisfies the `V_d(1)` Ward identity
(10.1) and `w` is a singular vector with `η(w, v_ν) = 0`, then `U(Vir_-) w ⊂ rad η`.
-/

namespace Virasoro

namespace Verma

variable {c ν d : ℂ} {η : Verma ℂ c ν →ₗ[ℂ] Verma ℂ c ν →ₗ[ℂ] ℂ}

/-- First induction (l.2404–2406): for `L_n a = 0` (`n > 0`), `L_0 a = λ a` and
`η(a, v_ν) = 0`, the Ward identity gives `η(a, L_{-n} u) = -(…) η(a, u)`, hence
`η(a, M(c,ν)) = 0`. -/
theorem ward_right_zero
    (hW : ∀ (n : ℤ) (u v : Verma ℂ c ν),
      η (L (-n) u) v - η u (L n v) = η (L 0 u) v - η u (L 0 v) + (n : ℂ) * d * η u v)
    {a : Verma ℂ c ν} {lam : ℂ} (ha0 : L 0 a = lam • a) (hapos : ∀ n : ℤ, 0 < n → L n a = 0)
    (ha : η a hw = 0) : ∀ v, η a v = 0 := by
  refine induction_neg (fun w hw => ?_) (fun u v hu hv => by rw [map_add, hu, hv, add_zero])
    (fun r v hv => by rw [map_smul, hv, smul_zero])
  induction w with
  | nil => rw [neg_nil]; exact ha
  | cons m w ih =>
    have hm : 0 < m := hw m List.mem_cons_self
    have hw' : PosWord w := fun z hz => hw z (List.mem_cons_of_mem _ hz)
    have e := hW (-(m : ℤ)) a (neg w)
    rw [neg_neg, hapos _ (by omega), ha0, L_zero_neg, map_zero, LinearMap.zero_apply, map_smul,
      map_smul, LinearMap.smul_apply, ← neg_cons, ih hw'] at e
    simpa using e

/-- Second induction on the PBW length (l.2406–2409). -/
theorem ward_negOp_zero
    (hW : ∀ (n : ℤ) (u v : Verma ℂ c ν),
      η (L (-n) u) v - η u (L n v) = η (L 0 u) v - η u (L 0 v) + (n : ℂ) * d * η u v)
    {w : Verma ℂ c ν} {ℓ : ℕ} (hw : IsSingular w ℓ) (h0 : η w Verma.hw = 0) :
    ∀ l : List ℕ+, (∀ v, η (VirEnv.negOp c (l.map PNat.val) • w) v = 0) ∧
      ∃ lam : ℂ, L 0 (VirEnv.negOp c (l.map PNat.val) • w) = lam • (VirEnv.negOp c (l.map PNat.val) • w) := by
  intro l
  induction l with
  | nil =>
    have e : VirEnv.negOp c (([] : List ℕ+).map PNat.val) • w = w := by
      simp [VirEnv.negOp]
    rw [e]
    exact ⟨ward_right_zero hW hw.2.1 hw.2.2 h0, _, hw.2.1⟩
  | cons y l ih =>
    obtain ⟨h1, lam, ha0⟩ := ih
    have e : VirEnv.negOp c ((y :: l).map PNat.val) • w =
        L (-((y : ℕ) : ℤ)) (VirEnv.negOp c (l.map PNat.val) • w) := by
      have e' : VirEnv.negOp c ((y : ℕ) :: l.map PNat.val) =
          VirEnv.L c (-((y : ℕ) : ℤ)) * VirEnv.negOp c (l.map PNat.val) := by
        simp [VirEnv.negOp]
      rw [List.map_cons, e', mul_smul]
      rfl
    rw [e]
    refine ⟨fun v => ?_, lam - ((-((y : ℕ) : ℤ) : ℤ) : ℂ), ?_⟩
    · have e2 := hW ((y : ℕ) : ℤ) (VirEnv.negOp c (l.map PNat.val) • w) v
      rw [h1 (L (((y : ℕ) : ℤ)) v), ha0, LinearMap.map_smul, LinearMap.smul_apply, h1 v,
        h1 (L 0 v)] at e2
      simpa using e2
    · have h := L_L_zero (-((y : ℕ) : ℤ)) (VirEnv.negOp c (l.map PNat.val) • w)
      rw [ha0, LinearMap.map_smul] at h
      rw [eq_sub_of_add_eq h.symm]
      module

/-- The Ward-induction fact (l.2401–2410). -/
theorem ward_induction
    (hW : ∀ (n : ℤ) (u v : Verma ℂ c ν),
      η (L (-n) u) v - η u (L n v) = η (L 0 u) v - η u (L 0 v) + (n : ℂ) * d * η u v)
    (hsym : ∀ u v, η u v = η v u) {w : Verma ℂ c ν} {ℓ : ℕ} (hw : IsSingular w ℓ)
    (h0 : η w Verma.hw = 0) : ∀ u ∈ negSpan w, ∀ v, η u v = 0 ∧ η v u = 0 := by
  have key : ∀ u ∈ negSpan w, ∀ v, η u v = 0 := by
    intro u hu
    refine Submodule.span_induction (p := fun u _ => ∀ v, η u v = 0) ?_ ?_ ?_ ?_ hu
    · rintro u ⟨l, rfl⟩
      exact (ward_negOp_zero hW hw h0 l).1
    · intro v
      rw [map_zero, LinearMap.zero_apply]
    · intro x y _ _ hx hy v
      rw [map_add, LinearMap.add_apply, hx v, hy v, add_zero]
    · intro r x _ hx v
      rw [map_smul, LinearMap.smul_apply, hx v, smul_zero]
  intro u hu v
  exact ⟨key u hu v, by rw [← hsym]; exact key u hu v⟩

end Verma

end Virasoro
