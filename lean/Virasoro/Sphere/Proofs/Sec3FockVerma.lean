import Virasoro.Sphere.Statements.Sec3a
import Virasoro.Sphere.Proofs.Sec3WardBlock

/-!
# Sphere paper Lemma 3.2, parts (i) and (ii) assembled

Parts (i) and (ii) of the frozen statement `Stmt_lem_fock_verma` from the two cited inputs the
paper's proof uses: the Feigin–Fuchs operators (sphere/paper.tex l.428, l.443–444) and the Kac
determinant (l.471–480).  Part (iii) enters as the hypothesis `h3`.
-/

namespace Virasoro.Sphere

open MvPolynomial Verma

theorem lem_fock_verma_of_iii (hF : Cited_FeiginFuchsOperators) (hK : Cited_KacDeterminant)
    (h3 : ∀ N : ℕ,
      (∀ μ : ℝ, 0 < μ → ∀ Δe : Fin 4 → ℝ,
        Filter.Tendsto
          (fun lam : ℝ => RatFunc.eval (RingHom.id ℂ) ((lam : ℂ) ^ 2 + (μ : ℂ) ^ 2)
            (Hsph (1 + 24 * (μ : ℂ) ^ 2) (fun i => (Δe i : ℂ)) N))
          Filter.atTop (nhds (if N = 0 then 1 else 0))) →
      LargeDeltaAt N) : Stmt_lem_fock_verma := by
  refine ⟨fun μ hμ lam hlam => ?_, h3⟩
  dsimp only
  refine ⟨⟨fun N => gram_det_ne_zero_fock hK μ lam hμ hlam N,
    fun N N' Y Y' => fockForm_fockWord hF μ lam Y.word Y'.word (posWord_word Y'),
    fun N f hf => level_basis (fun Y : Nat.Partition N => fockWord (μ : ℂ) (lam : ℂ) Y.word)
      (fun Y => fw_mem_level μ lam Y) _ (gram_det_ne_zero_fock hK μ lam hμ hlam N)
      (fun Y Y' => fock_gram_iso hF μ lam Y Y') f hf⟩,
    fun Δe => ⟨ward_existsUnique hF hK μ lam hμ hlam _ _,
      fun F G h1 h2 N => block_eq_fockBil hF hK μ lam hμ hlam Δe F G h1 h2 N⟩⟩

end Virasoro.Sphere
