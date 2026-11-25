module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatSmulMem
public import Mathlib.NumberTheory.NumberField.Basic
import Supplements.MathlibImports.AnalysisAndTactics
import Mathlib.RingTheory.SimpleRing.Principal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenExists

@[expose] public section

namespace GlobalTheory.IntegralMultipleClearDenominators

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := GlobalTheory.DenominatorExistence.den_exists c

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  apply PI.WAU.exists_nat_smul_mem <;> assumption

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx

end GlobalTheory.IntegralMultipleClearDenominators
