module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PowCardLeIndexIInfOfPrime
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.pow_card_le_index_iInf_of_prime' : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime → (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  first | exact @GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime | exact GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime | (intros; apply GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime <;> assumption)
