import Virasoro.Proofs.Sec7Val
import Virasoro.Proofs.Sec7Pole
import Virasoro.Proofs.Sec6Kac
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Germs: values at `t = 0`, naturality under field homomorphisms, transcendence of `b⋆ + t`
-/

namespace Virasoro

open scoped LaurentSeries

section Hom

variable {F F' : Type*} [Field F] [Field F'] (φ : F →+* F')

theorem map_kacC (b : F) : φ (kacC b) = kacC (φ b) := by
  simp [kacC, map_inv₀, map_ofNat]

theorem map_kacH (r s : ℤ) (b : F) : φ (kacH r s b) = kacH r s (φ b) := by
  simp [kacH, map_inv₀, map_div₀, map_ofNat]

theorem map_kacHL (a : Label) (b : F) : φ (kacHL a b) = kacHL a (φ b) := map_kacH φ _ _ b

theorem map_genP (r s : ℕ) (b d : F) : φ (genP r s b d) = genP r s (φ b) (φ d) := by
  simp [genP, lamSq, map_inv₀, map_div₀, map_prod, map_ofNat]

theorem map_genA (r s : ℕ) (b : F) : φ (genA r s b) = genA r s (φ b) := by
  simp [genA, map_inv₀, map_prod, map_ofNat]

theorem map_genR (r s : ℕ) (b d : F) : φ (genR r s b d) = genR r s (φ b) (φ d) := by
  rw [genR, map_mul, map_genA, map_genP, genR]

end Hom

variable {K : Type*} [Field K]

/-- `x` is regular at `t = 0` with value `v`. -/
def RegVal (x : K⸨X⸩) (v : K) : Prop := OrdGE x 0 ∧ x.coeff 0 = v

theorem RegVal.add {x y : K⸨X⸩} {u v : K} (hx : RegVal x u) (hy : RegVal y v) :
    RegVal (x + y) (u + v) :=
  ⟨hx.1.add hy.1, by rw [HahnSeries.coeff_add, hx.2, hy.2]⟩

theorem RegVal.sub {x y : K⸨X⸩} {u v : K} (hx : RegVal x u) (hy : RegVal y v) :
    RegVal (x - y) (u - v) :=
  ⟨hx.1.sub hy.1, by rw [HahnSeries.coeff_sub, hx.2, hy.2]⟩

theorem regVal_C (c : K) : RegVal (HahnSeries.C c : K⸨X⸩) c :=
  ⟨ordGE_C c, by simp [HahnSeries.C]⟩

theorem RegVal.mul {x y : K⸨X⸩} {u v : K} (hx : RegVal x u) (hy : RegVal y v) :
    RegVal (x * y) (u * v) := by
  refine ⟨by simpa using hx.1.mul hy.1, ?_⟩
  have h := coeff_mul_congr (A := HahnSeries.C u) (A' := x) (S := HahnSeries.C v) (S' := y)
    (a := 0) (s := 0) (U := 0) (ordGE_C u) hy.1
    (fun n hn => by
      rcases lt_or_eq_of_le (show n ≤ 0 by simpa using hn) with h | h
      · rw [hx.1.coeff_eq_zero h, (ordGE_C u).coeff_eq_zero h]
      · rw [h, hx.2, (regVal_C u).2])
    (fun n hn => by
      rcases lt_or_eq_of_le (show n ≤ 0 by simpa using hn) with h | h
      · rw [hy.1.coeff_eq_zero h, (ordGE_C v).coeff_eq_zero h]
      · rw [h, hy.2, (regVal_C v).2])
    0 le_rfl
  rw [h, ← map_mul]
  exact (regVal_C (u * v)).2

theorem RegVal.inv {x : K⸨X⸩} {u : K} (hx : RegVal x u) (hu : u ≠ 0) : RegVal x⁻¹ u⁻¹ := by
  have hord : x.order = 0 := order_eq_zero_of hx.1 (by rw [hx.2]; exact hu)
  have hne : x ≠ 0 := by
    intro h
    have := hx.2
    rw [h] at this
    exact hu (by simpa using this.symm)
  have hinv : OrdGE x⁻¹ 0 := by
    have := ordGE_inv x
    rwa [hord, neg_zero] at this
  refine ⟨hinv, ?_⟩
  have hmul := (hx.mul (⟨hinv, rfl⟩ : RegVal x⁻¹ (x⁻¹.coeff 0))).2
  rw [mul_inv_cancel₀ hne] at hmul
  have h1 : (1 : K⸨X⸩).coeff 0 = 1 := by simp [HahnSeries.coeff_one]
  rw [h1] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

theorem RegVal.div {x y : K⸨X⸩} {u v : K} (hx : RegVal x u) (hy : RegVal y v) (hv : v ≠ 0) :
    RegVal (x / y) (u / v) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact hx.mul (hy.inv hv)

theorem RegVal.pow {x : K⸨X⸩} {u : K} (hx : RegVal x u) (n : ℕ) : RegVal (x ^ n) (u ^ n) := by
  induction n with
  | zero => simpa using regVal_C (1 : K)
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hx

theorem regVal_intCast (n : ℤ) : RegVal ((n : K⸨X⸩)) (n : K) := by
  have : ((n : K⸨X⸩)) = HahnSeries.C (n : K) := (map_intCast (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]; exact regVal_C _

theorem regVal_natCast (n : ℕ) : RegVal ((n : K⸨X⸩)) (n : K) := by
  have : ((n : K⸨X⸩)) = HahnSeries.C (n : K) := (map_natCast (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]; exact regVal_C _

theorem regVal_ofNat (n : ℕ) [n.AtLeastTwo] :
    RegVal ((OfNat.ofNat n : K⸨X⸩)) (OfNat.ofNat n : K) := by
  have : ((OfNat.ofNat n : K⸨X⸩)) = HahnSeries.C (OfNat.ofNat n : K) :=
    (map_ofNat (HahnSeries.C : K →+* K⸨X⸩) n).symm
  rw [this]; exact regVal_C _

theorem RegVal.prod {α : Type*} {s : Finset α} {f : α → K⸨X⸩} {v : α → K}
    (h : ∀ i ∈ s, RegVal (f i) (v i)) : RegVal (∏ i ∈ s, f i) (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regVal_C (1 : K)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem regVal_bGerm (bs : K) : RegVal (bGerm bs) bs := ⟨ordGE_bGerm bs, bGerm_coeff_zero bs⟩

section CharZero

variable [CharZero K]

/-- `h_{r,s}(b⋆ + t)` is regular at `t = 0` with value `h_{r,s}(b⋆)`. -/
theorem regVal_kacH {bs : K} (hbs : bs ≠ 0) (r s : ℤ) :
    RegVal (kacH r s (bGerm bs)) (kacH r s bs) := by
  have hb := regVal_bGerm bs
  have hbi := hb.inv hbs
  unfold kacH
  exact ((((hb.add hbi).pow 2).sub ((((regVal_intCast r).mul hb).add
    ((regVal_intCast s).mul hbi)).pow 2))).div (regVal_ofNat 4) (by norm_num)

theorem regVal_hG {bs : K} (hbs : bs ≠ 0) (a : Label) : RegVal (hG bs a) (kacHL a bs) :=
  regVal_kacH hbs _ _

theorem regVal_zG {bs : K} (hbs : bs ≠ 0) (a : Label) :
    RegVal (zG bs a) (kacHL a bs + (a.lvl : K)) :=
  (regVal_hG hbs a).add (regVal_natCast _)

/-- `𝒫_{r,s}(b⋆ + t, d)` is regular at `t = 0` with value `𝒫_{r,s}(b⋆, d)`. -/
theorem regVal_genP {bs : K} (hbs : bs ≠ 0) (d : K) (r s : ℕ) :
    RegVal (genP r s (bGerm bs) (HahnSeries.C d)) (genP r s bs d) := by
  have hb := regVal_bGerm bs
  have hbi := hb.inv hbs
  have hlam : RegVal (lamSq (bGerm bs) (HahnSeries.C d)) (lamSq bs d) := by
    unfold lamSq
    exact ((hb.add hbi).pow 2).sub ((regVal_ofNat 4).mul (regVal_C d))
  unfold genP
  refine RegVal.prod fun k _ => RegVal.prod fun l _ => ?_
  exact ((hlam.sub ((((regVal_natCast k).mul hb).add ((regVal_natCast l).mul hbi)).pow 2)).div
      (regVal_ofNat 4) (by norm_num)).mul
    ((hlam.sub ((((regVal_natCast k).mul hb).sub ((regVal_natCast l).mul hbi)).pow 2)).div
      (regVal_ofNat 4) (by norm_num))

/-- `𝒜_{r,s}(b⋆ + t)` is regular at `t = 0` when `b⋆²` is irrational. -/
theorem regVal_genA {bs : K} (hbs : bs ≠ 0) (hirr : SqIrrational bs) (r s : ℕ) :
    RegVal (genA r s (bGerm bs)) (genA r s bs) := by
  have hb := regVal_bGerm bs
  have hbi := hb.inv hbs
  unfold genA
  refine ((regVal_ofNat 2).inv (by norm_num)).mul (RegVal.prod fun pq hpq => ?_)
  exact (((regVal_intCast pq.1).mul hb).add ((regVal_intCast pq.2).mul hbi)).inv
    (genA_factor_ne hbs hirr _ _ (mem_genAIndex hpq))

theorem regVal_RG {bs : K} (hbs : bs ≠ 0) (hirr : SqIrrational bs) (d : K) (a : Label) :
    RegVal (RG bs d a) (genR a.1 a.2 bs d) :=
  (regVal_genA hbs hirr _ _).mul (regVal_genP hbs d _ _)

end CharZero

/-! ### The germ `b⋆ + t` is transcendental over `ℚ` -/

open Polynomial in
theorem bGerm_eq_coe (bs : K) :
    bGerm bs = HahnSeries.ofPowerSeries ℤ K ((X + C bs : K[X]) : PowerSeries K) := by
  rw [bGerm]
  simp [HahnSeries.ofPowerSeries_X, add_comm]

open Polynomial in
theorem aeval_bGerm_ne_zero [CharZero K] (bs : K) {P : ℚ[X]} (hP : P ≠ 0) :
    aeval (bGerm bs) P ≠ 0 := by
  -- the ring homomorphism `K[X] → K⸨X⸩`
  let ψ : K[X] →+* K⸨X⸩ :=
    (HahnSeries.ofPowerSeries ℤ K).comp (Polynomial.coeToPowerSeries.ringHom)
  have hψinj : Function.Injective ψ :=
    HahnSeries.ofPowerSeries_injective.comp (Polynomial.coe_injective K)
  have hb : bGerm bs = ψ (X + C bs) := bGerm_eq_coe bs
  have h1 : aeval (bGerm bs) P = ψ ((P.map (algebraMap ℚ K)).comp (X + C bs)) := by
    rw [hb, aeval_def, comp, eval₂_map, hom_eval₂]
    congr 1
    exact RingHom.ext fun q => by simp
  rw [h1]
  intro h0
  have h2 : (P.map (algebraMap ℚ K)).comp (X + C bs) = 0 := hψinj (by rw [h0, map_zero])
  have h3 : P.map (algebraMap ℚ K) = 0 := by
    have ht : taylor bs (P.map (algebraMap ℚ K)) = 0 := by rw [taylor_apply]; exact h2
    exact taylor_injective bs (by rw [ht, map_zero])
  exact hP (Polynomial.map_injective _ (algebraMap ℚ K).injective (by rw [h3, Polynomial.map_zero]))

end Virasoro
