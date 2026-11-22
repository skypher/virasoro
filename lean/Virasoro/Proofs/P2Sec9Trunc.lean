import Virasoro.Proofs.P2Sec9TruncEval
import Virasoro.Proofs.P2Sec9Collision
import Virasoro.Proofs.P2Sec11JointRec
import Virasoro.Proofs.Sec4Core1
import Virasoro.Proofs.Sec6Kac
import Virasoro.Proofs.GenericH

/-!
# Corollary 9.4: the truncated recursion at `b = b⋆` (paper.tex l.1975–1978, 3153–3157)

The generic recursion for `H_N(c(b),Δ,d(b))` over `ℂ(b)` has only the active terms.  When the
active multipliers are regular at `b⋆` and no shifted weight of an active label is an active
pole at `b⋆`, every denominator of the truncated recursion is nonzero at `b⋆`, and the recursion
specializes to `b = b⋆`, level by level.
-/

namespace Virasoro.P2

open Virasoro Polynomial

open Classical in
/-- The right-hand side of the truncated recursion at `b⋆`. -/
noncomputable def truncRHS (b : ℂ) (u v : ℤ) (act : Label → Prop) (N : ℕ) : RatFunc ℂ :=
  ∑ a ∈ (labels N).filter act,
    RatFunc.C (RatFunc.eval (RingHom.id ℂ) b
        (genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ)))) /
      (RatFunc.X - RatFunc.C (kacHL a b)) *
    RatFunc.C (RatFunc.eval (RingHom.id ℂ) (kacHL a b + (a.lvl : ℂ))
      (Hrat (kacC b) (kacH u v b) (N - a.lvl)))

open Classical in
/-- The value of the truncated right-hand side at a point that is no active pole. -/
theorem truncRHS_eval (b : ℂ) (u v : ℤ) (act : Label → Prop) (N : ℕ) {z : ℂ}
    (hz : ∀ a ∈ labels N, act a → z ≠ kacHL a b) :
    RegAt z (truncRHS b u v act N) ∧
      evalAt z (truncRHS b u v act N) =
        ∑ a ∈ (labels N).filter act,
          RatFunc.eval (RingHom.id ℂ) b
              (genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ))) /
            (z - kacHL a b) *
          RatFunc.eval (RingHom.id ℂ) (kacHL a b + (a.lvl : ℂ))
            (Hrat (kacC b) (kacH u v b) (N - a.lvl)) := by
  have hz' : ∀ a ∈ (labels N).filter act, z ≠ kacHL a b := fun a ha =>
    hz a (Finset.mem_filter.1 ha).1 (Finset.mem_filter.1 ha).2
  unfold truncRHS
  refine ⟨RegAt.sum fun a ha => regAt_pole_mul (hz' a ha) _ _, ?_⟩
  rw [evalAt_sum fun a ha => regAt_pole_mul (hz' a ha) _ _]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hC : ∀ s : ℂ, RegAt z (RatFunc.C s) ∧ evalAt z (RatFunc.C s) = s := fun s => by
    rw [← RatFunc.algebraMap_C]
    exact ⟨regAt_algebraMap z _, by rw [evalAt_algebraMap, eval_C]⟩
  rw [evalAt_mul (regAt_pole (hz' a ha) _).1 (hC _).1, (regAt_pole (hz' a ha) _).2, (hC _).2]

theorem labels_mono {M N : ℕ} (h : M ≤ N) : labels M ⊆ labels N := fun a ha =>
  mem_labels.2 ⟨(mem_labels.1 ha).1, (mem_labels.1 ha).2.1, (mem_labels.1 ha).2.2.trans h⟩

theorem kacHL_add_lvl {b : ℂ} (hb : b ≠ 0) (a : Label) :
    kacHL a b + (a.lvl : ℂ) = kacH (a.1 : ℤ) (-(a.2 : ℤ)) b := by
  simp only [kacHL, kacH, Label.lvl]
  push_cast
  field_simp
  ring

set_option maxHeartbeats 800000 in
open Classical in
/-- The truncated recursion at `b⋆` from the two obstructions it uses (l.3153–3157): the active
multipliers are regular at `b⋆`, the inactive ones vanish identically, and no shifted weight of
an active label is an active pole. -/
theorem truncRec_of_obstructions (hK : Cited_KacDeterminant) (hH : Cited_HJSNormalizations)
    {b : ℂ} (hb : b ≠ 0) (u v : ℤ) (act : Label → Prop)
    (hin : ∀ a : Label, 0 < a.1 → 0 < a.2 → ¬act a →
      genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ)) = 0)
    (h1 : ∀ a : Label, 0 < a.1 → 0 < a.2 → act a →
      (genR a.1 a.2 (RatFunc.X : RatFunc ℂ) (kacH u v (RatFunc.X : RatFunc ℂ))).denom.eval b ≠ 0)
    (h3 : ∀ a a' : Label, 0 < a.1 → 0 < a.2 → act a → 0 < a'.1 → 0 < a'.2 → act a' →
      kacH (a.1 : ℤ) (-(a.2 : ℤ)) b ≠ kacHL a' b) :
    TruncRecAt b u v act := by
  set bX : RatFunc ℂ := RatFunc.X with hbX
  set dX : RatFunc ℂ := kacH u v bX with hdX
  have hbX0 : bX ≠ 0 := RatFunc.X_ne_zero
  have hc : EvToK b (kacC bX) (kacC b) := evToK_kacC hb
  have hd : EvToK b dX (kacH u v b) := evToK_kacH hb u v
  have hgen : ∀ N, 1 ≤ N → GenericRecursionAt (RatFunc ℂ) bX dX N := by
    intro N hN
    obtain ⟨S, hS0, hS⟩ := genericRecursionUniform hK hH N hN
    exact hS (RatFunc ℂ) bX dX hbX0 fun P hP => aeval_ratFuncX_ne_zero (hS0 P hP)
  have hR : ∀ a : Label, 0 < a.1 → 0 < a.2 → act a →
      EvToK b (genR a.1 a.2 bX dX) (RatFunc.eval (RingHom.id ℂ) b (genR a.1 a.2 bX dX)) :=
    fun a p1 p2 ha => ⟨h1 a p1 p2 ha, rfl⟩
  have key : ∀ N : ℕ,
      (1 ≤ N → Hrat (kacC b) (kacH u v b) N = truncRHS b u v act N) ∧
      ∀ δ : RatFunc ℂ, ∀ δv : ℂ, EvToK b δ δv → (∀ a ∈ labels N, δ ≠ kacHL a bX) →
        (∀ a ∈ labels N, act a → δv ≠ kacHL a b) →
          EvToK b (evalAt δ (Hrat (kacC bX) dX N)) (evalAt δv (Hrat (kacC b) (kacH u v b) N)) := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    by_cases hN0 : N = 0
    · subst hN0
      refine ⟨fun h => absurd h (by norm_num), fun δ δv _ _ _ => ?_⟩
      rw [Hrat_zero, Hrat_zero]
      have e1 : evalAt δ (1 : RatFunc (RatFunc ℂ)) = 1 := RatFunc.eval_one _ _
      have e2 : evalAt δv (1 : RatFunc ℂ) = 1 := RatFunc.eval_one _ _
      rw [e1, e2]
      exact evToK_one
    have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.2 hN0
    have hA : ∀ δ : RatFunc ℂ, ∀ δv : ℂ, EvToK b δ δv → (∀ a ∈ labels N, δ ≠ kacHL a bX) →
        (∀ a ∈ labels N, act a → δv ≠ kacHL a b) →
          EvToK b (evalAt δ (Hrat (kacC bX) dX N)) (evalAt δv (truncRHS b u v act N)) := by
      intro δ δv hδ hgenne hactne
      rw [evalAt_recursion (hgen N hN) hgenne, (truncRHS_eval b u v act N hactne).2,
        ← Finset.sum_filter_add_sum_filter_not (labels N) act]
      have hzero : ∑ a ∈ (labels N).filter (fun a => ¬act a),
          genR a.1 a.2 bX dX / (δ - kacHL a bX) *
            evalAt (kacHL a bX + (a.lvl : RatFunc ℂ)) (Hrat (kacC bX) dX (N - a.lvl)) = 0 := by
        refine Finset.sum_eq_zero fun a ha => ?_
        rw [Finset.mem_filter] at ha
        obtain ⟨p1, p2, -⟩ := label_pos ha.1
        rw [hin a p1 p2 ha.2, zero_div, zero_mul]
      rw [hzero, add_zero]
      refine evToK_sum _ fun a ha => ?_
      rw [Finset.mem_filter] at ha
      obtain ⟨p1, p2, p3⟩ := label_pos ha.1
      have hlt : N - a.lvl < N := by
        have : 0 < a.lvl := Nat.mul_pos p1 p2
        omega
      refine ((hR a p1 p2 ha.2).div (hδ.sub (evToK_kacH hb _ _))
        (sub_ne_zero.2 (hactne a ha.1 ha.2))).mul ?_
      refine (ih (N - a.lvl) hlt).2 _ _ ((evToK_kacH hb _ _).add (evToK_natCast _)) ?_ ?_
      · intro a' ha' heq
        obtain ⟨q1, q2, -⟩ := label_pos ha'
        have hne := kacH_shift_ne hbX0 sqIrrational_ratFuncX (a.1 : ℤ) (a.2 : ℤ) (a'.1 : ℤ)
          (a'.2 : ℤ) (by exact_mod_cast p1) (by exact_mod_cast p2) (by exact_mod_cast q1)
          (by exact_mod_cast q2)
        apply hne
        simp only [kacHL, Label.lvl] at heq
        rw [← heq]
        push_cast
        ring
      · intro a' ha' hact'
        obtain ⟨q1, q2, -⟩ := label_pos ha'
        rw [kacHL_add_lvl hb]
        exact h3 a a' p1 p2 ha.2 q1 q2 hact'
    have hB : Hrat (kacC b) (kacH u v b) N = truncRHS b u v act N := by
      refine ratFunc_eq_of_evalAt ((labels N).image fun a => kacHL a b) fun z hz => ?_
      have hzne : ∀ a ∈ labels N, kacHL a b ≠ z := fun a ha heq =>
        hz (Finset.mem_image.2 ⟨a, ha, heq⟩)
      have hdet : ∀ M ≤ N, (gram (kacC b) z M).det ≠ 0 := fun M hM =>
        gram_det_ne_of_labels hK hb fun g hg => hzne g (labels_mono hM hg)
      have hCz : EvToK b (RatFunc.C z) z := evToK_C (K := ℂ) (b := b) z
      have hgenne : ∀ a ∈ labels N, RatFunc.C z ≠ kacHL a bX := by
        intro a ha heq
        have h2 : EvToK b (kacHL a bX) (kacHL a b) := evToK_kacH hb _ _
        rw [← heq] at h2
        exact hzne a ha (evToK_uniq h2 hCz)
      have hdetX : ∀ M ≤ N, (gram (kacC bX) (RatFunc.C z) M).det ≠ 0 := fun M hM =>
        gram_det_ne_of_labels hK hbX0 fun g hg => (hgenne g (labels_mono hM hg)).symm
      have hrhs := truncRHS_eval b u v act N (z := z) fun a ha _ => (hzne a ha).symm
      refine ⟨regAt_Hrat hdet, hrhs.1, ?_⟩
      have e1 := hA (RatFunc.C z) z hCz hgenne fun a ha _ => (hzne a ha).symm
      rw [evalAt_Hrat hdetX] at e1
      rw [evalAt_Hrat hdet]
      exact evToK_uniq (evToK_Hval hc hd hCz N hdet) e1
    refine ⟨fun _ => hB, fun δ δv hδ hgenne hactne => ?_⟩
    rw [hB]
    exact hA δ δv hδ hgenne hactne
  intro N hN
  exact (key N).1 hN

end Virasoro.P2
